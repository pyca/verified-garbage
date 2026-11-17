module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.MdHmac
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.X86.Compress

/-! ### `Pbkdf2.Stream.X86.Finalize`, which this module and modules that import it used -/

section

/-!
# HMAC on x86 (32-bit): the start of `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86.lean`) starts by finalizing the inner
state with the hash function's streaming `finalize`, called with the code of
`Impl/Pbkdf2/Stream/X86.lean`: the prologue (`pro_ok`) loads `scratch`,
`inner`, `outer` and `out` (after our caller's registers are saved in
`scratch`), and the count just before the call, which passes it on
(`fin1Args_ok`, `finCall_ok`). What the rest keeps is `KR`;
`Proof/Pbkdf2/Md/X86/HmacFin.lean` continues from there.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Stream.X86.Finalize

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash copy at_)
open VG.Proof.Pbkdf2.Stream.X86
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 sub_of_off sub_of_self bytes_keep
  bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev outer : BitVec 32 := arg s₀ 1
abbrev op : BitVec 32 := arg s₀ 4
abbrev scr : BitVec 32 := arg s₀ 5
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.S⟩
abbrev outerR : Region := ⟨(outer s₀).setWidth 64, H.S⟩
abbrev opR : Region := ⟨(op s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- Where the digests go. -/
abbrev T : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨(scr s₀).setWidth 64, hH.Wb⟩
/-- `T`, as a register holds it. -/
abbrev tO : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.buf

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outerR (H := H) s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outerR (H := H) s₀)
  i_p : (inR (H := H) s₀).Disjoint (opR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_p : (outerR (H := H) s₀).Disjoint (opR (H := H) s₀)
  o_s : (outerR (H := H) s₀).Disjoint (scR sc s₀)
  p_s : (opR (H := H) s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_p : (argR s₀).Disjoint (opR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_p : (retR s₀).Disjoint (opR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  b_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (outer s₀).toNat + H.S ≤ 2 ^ 32
  np : (op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 28 ≤ 2 ^ 32
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h22]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, hfit, ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Hash.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 16) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hD
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.hW; have := hp.hD
  exact off_disj _ (a := 8 * H.W) (m := 16) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

theorem addr_tO : (tO (H := H) s₀).setWidth 64 = T (H := H) s₀ :=
  setWidth_add (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem toNat_tO : (tO (H := H) s₀).toNat = (scr s₀).toNat + H.buf :=
  toNat_add_ofNat (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega_nat)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega_nat)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  ebx : s.gpr .ebx = inn s₀
  edi : s.gpr .edi = op s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .edi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide
section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.edi, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega_nat) (by have := hp.spf; omega_nat)⟩

theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 24) (by have := hp.spf; omega_nat) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_p
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega_nat)

theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_p
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

/-- `KR` after a call that writes `rs`, parts of our buffers, and keeps `esi`. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, Region.Sub r (scR sc s₀) ∨ r = inR (H := H) s₀) :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · rcases hsub r hr with h | rfl
      · exact ⟨scR sc s₀, by simp, h⟩
      · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-! ## The pieces -/

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀ ∧
    Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw; have hD := hp.hD
  simp only [Hash.buf] at hf
  obtain ⟨sR, _, _⟩ := wr_mem hp
  have dA : ∀ r ∈ [saveR H (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  simp only [Hash.finPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 5) (argW rfl 5) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_nat) (by omega_nat)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega_nat) (by have := hp.spf; omega_nat))) (by decide)
  have i₂ : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by
      rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 4 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)],
    by rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, rA 4 (by decide)],
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩⟩,
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)], hm ▸ f₂'⟩

/-- The arguments of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) sc s₀ t) {lo hi : BitVec 32} (hax : t.gpr .eax = lo)
    (hcx : t.gpr .ecx = hi) (hdx : t.gpr .edx = tO (H := H) s₀) :
    FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) lo hi := by
  have hwb := hH.hWb; have hf := hp.fits; have hf' := hp.fits; have hD := hp.hD; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { hst := hk.ebx, eax := hax, ecx := hcx, edx := hdx, ebp := hk.ebp, hr := by decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by
        rw [hk.wr, addr_tO hp]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := by rw [addr_tO hp]; exact hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := by rw [addr_tO hp]; exact (cal_t hH hp).symm
      b_st := by rw [stk_eq hk]; exact hp.b_i
      b_o := by rw [stk_eq hk, addr_tO hp]; exact hp.b_s.sub_right (t_sub hp)
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := hp.ni
      no := by rw [toNat_tO hp]; omega_nat
      nsc := by omega_nat }

/-- The first call's arguments: the count from the stack. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block ([] ++ Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.buf)) s fun t =>
      KR (H := H) sc s₀ t ∧ FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧
        t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem := by
  simp only [Hash.count1, Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, hk.esp]; rfl) (argIn hp hk.rd hk.wr (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, u₁.other _ (by decide), hk.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact argIn hp hk.rd hk.wr (by decide)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
  have k₄ : KR (H := H) sc s₀ s₄ := (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.readArg hp (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hk.readArg hp (by decide)]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.ebp]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]

theorem finCall_ok {t : State} (hk : KR (H := H) sc s₀ t) {lo hi : BitVec 32}
    (ha : FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) lo hi) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .esi = t.gpr .esi →
      Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem ((inn s₀).setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push (fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (fin5 .ebx).length)) t Q :=
  fin_frame hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [stk_eq hk, addr_tO hp] at f
    rw [addr_tO hp] at hpost
    refine hQ s' (hk.call hp ha' ?_ ?_) (ha'.cs .esi (by simp [calleeSaved])) f hpost
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (save_sub hp)
      · exact save_t hp
      · exact (cal_save hH hp).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact .inr rfl
      · exact .inl (t_sub hp)
      · exact .inl (cal_sub hH hp)

end

end VG.Proof.Pbkdf2.Stream.X86.Finalize

end

end

/-!
# HMAC over a Merkle–Damgård hash function on x86 (32-bit): `finalize`, correct

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86.lean`) starts with the prologue and the
call of the hash function's streaming `finalize` on the inner state, which
writes the inner digest to `scratch` (`Proof/Pbkdf2/Md/X86/HmacFin.lean`,
whose `KR` the rest keeps). Then the inner state gets the outer hash value
and, in its buffer, the digest and the padding (`mid_ok`); one compression
(`cmpF_ok`) gives the outer hash value, whose digest is the MAC (`out_ok`):
`Md.Link.hmac_outer`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86.HmacFin

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash copyW)
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (HashOK finG SavedRegs saveR savedRegs restore_ok callee_saved ea_at stk After
  setWidth_add toNat_add_ofNat)
open VG.Proof.Pbkdf2.Stream.X86.Finalize (Pre KR E inn outer op scr inR outerR opR scR stkR T tR calR tO wr_mem
  save_sub t_sub save_t wrs kregs kregs_callee stk_eq pro_ok fin1Args_ok finCall_ok)
open VG.Proof.Hmac.Generic.Common (InRegions.right' bytesAt_writeBytes_self' bytesAt_take covers_one)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add bytesAt_writeBytes_sep writeBytes_at bytesAt_getD'
  xorPad_length)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre (H := H.st) sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 16 ∧ H.st.buf + H.st.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ 0 < H.N ∧ H.N ≤ 64 ∧ 0 < H.D ∧ H.D ≤ H.N ∧ H.B ≤ 128 ∧ 64 ≤ H.B ∧
    H.S = H.N + H.B ∧ H.D ≤ H.st.F ∧ (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (outer s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (op s₀).toNat + H.D ≤ 2 ^ 32 := by
  have hp_ni := hp.ni; have hp_no := hp.no; have hp_np := hp.np
  have hS := hz.S
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N.1, hz.N.2.1, hz.D.1, hz.D.2.1, hz.B4.2.2, hz.B4.2.1, hS, hz.F.1,
    by rw [← hS]; exact hp.ni, by rw [← hS]; exact hp.no, hp.np⟩

/-- The compression function's scratch space. -/
abbrev cmpR (H : Hash) (s₀ : State) : Region := ⟨(scr s₀).setWidth 64, H.so⟩

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega_using [this])

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (hz.so) (hz.buf_le64)

omit hp in
theorem inR_eq : inR (H := H.st) s₀ = ⟨(inn s₀).setWidth 64, H.N + H.B⟩ := by
  rw [inR, show H.st.S = H.N + H.B from hz.S]

/-- The inner state is writable. -/
theorem cov_in {s : State} (hwr : s.wr = s₀.wr) : Covers [⟨(inn s₀).setWidth 64, H.N + H.B⟩] s.wr := by
  rw [← inR_eq hz, hwr]
  exact covers_one (wr_mem hp).2.1

omit hp in
/-- A part of the inner state. -/
theorem in_sub {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ (inR (H := H.st) s₀) := by
  rw [inR_eq hz]; exact Offset.sub_base _ h

theorem save_in {a n : Nat} (h : a + n ≤ H.N + H.B) :
    (saveR H.st (scr s₀)).Disjoint ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ :=
  (hp.i_s.symm.sub_left (save_sub hp)).sub_right (in_sub hz h)

/-- `KR` after code that writes only a part of the inner state and `eax`,
`ecx` and `edx`. -/
theorem kr_write {s s' : State} (h : KR (H := H.st) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) {a n : Nat} (hl : a + n ≤ H.N + H.B)
    (hf : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩] s.mem s'.mem) : KR (H := H.st) sc s₀ s' :=
  h.keep hrd hwr (fun r hr => hg r (by revert hr; decide +revert) (by revert hr; decide +revert)
    (by revert hr; decide +revert)) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact save_in hz hp hl)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, in_sub hz hl⟩)

/-- The arguments of the compression of the inner buffer. -/
theorem cmpArgs {s : State} (hk : KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N) :
    CmpArgs H.N H.B H.so s (inn s₀) (scr s₀) := by
  have := bounds hz hp
  exact
    { ebx := hk.ebx, eax := hax, ebp := hk.ebp, sp48 := by rw [hk.esp]; exact hp.sp48
      cst := cov_in hz hp hk.wr
      csc := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨scR sc s₀, (wr_mem hp).1, 0, by simp, by simp only; omega_using [this]⟩
      st_sc := by rw [← inR_eq hz]; exact hp.i_s.sub_right (cmp_sub hz hp)
      b_st := by rw [stk_eq hk, ← inR_eq hz]; exact hp.b_i
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cmp_sub hz hp)
      nst := by omega_using [this]
      nsc := by omega_using [this] }

end

/-! ## The outer block -/

section
variable {H : Hash} (hO : MdOk H) {sc : Nat} {s₀ : State} (hp : Pre (H := H.st) sc s₀)
include hO hp

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and `eax` at the buffer. -/
theorem mid_ok {s : State} (hk : KR (H := H.st) sc s₀ s) (hsi : s.gpr .esi = outer s₀) :
    WP isa (.block H.finMid) s fun t => KR (H := H.st) sc s₀ t ∧ t.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N ∧
      hO.md.stateAt t.mem ((inn s₀).setWidth 64) = hO.md.stateAt s.mem ((outer s₀).setWidth 64) ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N) H.D = bytesAt s.mem (T (H := H.st) s₀) H.D ∧
      bytesAt t.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D)) (H.B - H.D) = H.tailB ∧
      Frame [inR (H := H.st) s₀] s.mem t.mem := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hN4 := hz.N.2.2; have hD4 := hz.D.2.2; have tl := hz.tail_length; have hDL := hz.DL
  have hn4 : 4 * (H.N / 4) = H.N := by omega_using [hN4]
  have hd4 : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  have oc : Covers [⟨(outer s₀).setWidth 64, H.N + H.B⟩] (s.rd ++ s.wr) :=
    covers_one (by rw [hk.rd, hp.rd, ← hS]; simp)
  have sc' : Covers [scR sc s₀] (s.rd ++ s.wr) := covers_one (by rw [hk.rd, hk.wr, hp.wr]; simp)
  have ic := cov_in hz hp hk.wr
  simp only [Hash.finMid, List.append_assoc]
  -- The outer hash value.
  refine copyW_ok (by decide) (by decide) (H.N / 4) _ s _ hsi hk.ebx (by omega_using [no]) (by omega_using [ni])
    (fun j hj => by rw [addr_eq (by omega_using [hj, no])]; exact inReg oc (by omega_using [hj]) (hz.NB_lt64))
    (fun j hj => by rw [addr_eq (by omega_using [hj, ni])]; exact inReg ic (by omega_using [hj]) (hz.NB_lt64)) ?_ fun s₁ g₁ rd₁ wr₁ m₁ => ?_
  · rw [hn4, BitVec.add_zero, BitVec.add_zero]
    have c₁ : (outerR (H := H.st) s₀).Contains ((outer s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega_using [])
    have c₂ : (inR (H := H.st) s₀).Contains ((inn s₀).setWidth 64) H.N :=
      Memory.contains_base (show H.N ≤ H.st.S by rw [show H.st.S = H.N + H.B from hz.S]; omega_using [])
    exact hp.i_o.symm.sep c₁ c₂
  rw [hn4, BitVec.add_zero, BitVec.add_zero] at m₁
  have f₁ : Frame [⟨(inn s₀).setWidth 64, H.N⟩] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The digest.
  refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₁ _ (by rw [g₁ _ (by decide), hk.ebp])
    (by rw [g₁ _ (by decide), hk.ebx]) (by omega_using [hDF, hw, hf]) (by omega_using [ni, hB64, hDN, hN])
    (fun j hj => by rw [addr_eq (by omega_using [hj, hDF, hw, hf]), rd₁, wr₁]; exact inReg sc' (by omega_using [hj, hDF, hf]) (by omega_using [hw]))
    (fun j hj => by rw [addr_eq (by omega_using [hj, ni, hB64, hDN, hN]), wr₁]; exact inReg ic (by omega_using [hj, hB64, hDN, hN]) (hz.NB_lt64)) ?_ fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  · rw [hd4]
    exact hp.i_s.symm.sep (Offset.contains_base _ (by omega_using [hDF, hf]) (by omega_using [hf, hw]))
      (by rw [inR_eq hz]; exact Offset.contains_base _ (hz.ND_le) (hz.N_lt64))
  rw [hd4] at m₂
  have f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.D⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  -- The padding, and `eax` at the buffer.
  refine pad_ok hz (x := inn s₀) (by rw [g₂ _ (by decide), g₁ _ (by decide), hk.ebx]) (by omega_using [ni])
    (by rw [wr₂, wr₁]; exact ic) fun s₃ g₃ rd₃ wr₃ m₃ => ?_
  rw [← List.append_nil H.atBlk]
  refine atBlk_ok fun s₄ e₄ g₄ m₄ rd₄ wr₄ => WP.block_nil ?_
  have f₃ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact writeBytes_frame _ _ _ (by rw [tl]; exact Region.contains_self _ _)
  have fI : Frame [inR (H := H.st) s₀] s.mem s₄.mem :=
    ((f₁.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rw [BitVec.add_zero] at this
        exact ⟨_, List.mem_singleton_self _, this⟩).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, in_sub hz (hz.ND_le)⟩)).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, in_sub hz (hz.NDB_le)⟩)
  have k₄ : KR (H := H.st) sc s₀ s₄ := hk.keep (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁])
    (fun r hr => by
      rw [g₄ r (by revert hr; decide +revert), g₃ r (by revert hr; decide +revert),
        g₂ r (by revert hr; decide +revert), g₁ r (by revert hr; decide +revert)]) fI
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.i_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
  -- The bytes before the padding are not written by it, and those before the digest not by it.
  have d₃ : ∀ {a n : Nat}, a + n ≤ H.N + H.D →
      ∀ r ∈ [(⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 (H.N + H.D), H.B - H.D⟩ : Region)],
        Region.Disjoint ⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl h) (by omega_using [h, hDN, hN]) (by omega_using [hB, hDN, hN])
  refine ⟨k₄, by rw [e₄, g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hk.ebx], ?_, ?_, ?_, fI⟩
  · refine hO.reloc _ _ _ _ fun i hi => ?_
    have dN : ∀ {a n : Nat}, H.N ≤ a → a + n ≤ H.N + H.B →
        ∀ r ∈ [(⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 a, n⟩ : Region)],
          Region.Disjoint ⟨(inn s₀).setWidth 64, H.N⟩ r := by
      intro a n h₁ h₂ r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ h₁ (by omega_using [h₂, hB, hN])
    rw [f₃.bytes (R := ⟨(inn s₀).setWidth 64, H.N⟩) (dN (Nat.le_add_right _ _) (hz.NDB_le)) (by show H.N ≤ 2 ^ 64; omega_using [hN]) hi,
      f₂.bytes (R := ⟨(inn s₀).setWidth 64, H.N⟩) (dN (by omega_using []) (hz.ND_le)) (by show H.N ≤ 2 ^ 64; omega_using [no]) hi, m₁,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hN]), bytesAt_getD' _ _ hi]
  · rw [Memory.frame_bytesAt f₃ (d₃ (by omega_using [])) (hz.D_le64), m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hz.D_lt64)]
    have dT : ∀ r ∈ [(⟨(inn s₀).setWidth 64, H.N⟩ : Region)], Region.Disjoint ⟨T (H := H.st) s₀, H.D⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      refine (hp.i_s.symm.sub_left fun a ha => t_sub hp a (Region.sub_prefix hDF a ha)).sub_right ?_
      rw [inR_eq hz]; exact Region.sub_prefix (Nat.le_add_right _ _)
    exact Memory.frame_bytesAt f₁ dT (hz.D_le64)
  · rw [m₄, m₃, ← tl, bytesAt_writeBytes_self' rfl (by omega_using [tl, hB])]

/-- The compression of the inner buffer into the outer hash value. -/
theorem cmpF_ok {s : State} (hk : KR (H := H.st) sc s₀ s) (hax : s.gpr .eax = inn s₀ + BitVec.ofNat 32 H.N)
    {Q : State → Prop}
    (k : ∀ s', KR (H := H.st) sc s₀ s' →
      Frame [⟨(inn s₀).setWidth 64, H.N⟩, cmpR H s₀, stkR s₀] s.mem s'.mem →
      hO.md.stateAt s'.mem ((inn s₀).setWidth 64) = hO.md.compress (hO.md.stateAt s.mem ((inn s₀).setWidth 64))
        (hO.md.blockAt s.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.cmp s Q := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, -⟩ := bounds hz hp
  have hB := hz.B4
  refine cmp_ok hO.comp (hz.B_pos) (cmpArgs hz hp hk hax) fun s₃ ha e₃ => ?_
  have f := ha.frame
  rw [stk_eq hk] at f
  have sI : Region.Sub ⟨(inn s₀).setWidth 64, H.N⟩ (inR (H := H.st) s₀) := by
    have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this
  refine k s₃ (hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_) (f.mono (by simp)) e₃
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact (hp.i_s.symm.sub_left (save_sub hp)).sub_right sI
    · exact save_cmp hz hp
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact ⟨_, by simp, sI⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {s : State} (hk : KR (H := H.st) sc s₀ s) :
    WP isa (.block H.finOut) s fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem ((op s₀).setWidth 64) H.D = (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hD4 := hz.D.2.2
  have hd4 : 4 * (H.D / 4) = H.D := by omega_using [hD4]
  have eD : H.st.D = H.D := rfl
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have ic := cov_in hz hp hk.wr
  have hdl := hO.md.digest_length (hO.md.stateAt s.mem ((inn s₀).setWidth 64))
  have sI : Region.Sub ⟨(inn s₀).setWidth 64, H.N⟩ (inR (H := H.st) s₀) := by
    have := in_sub hz (s₀ := s₀) (a := 0) (n := H.N) (by omega_using []); rwa [BitVec.add_zero] at this
  have hL : 8 * H.st.W + 16 ≤ 8 * sc := by omega_using [hf, hb]
  -- The epilogue, from the state the MAC is written in.
  have epi : ∀ t, KR (H := H.st) sc s₀ t → bytesAt t.mem ((op s₀).setWidth 64) H.D =
      (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D →
      WP isa (.block H.st.restore) t fun s' => abiPreserved s₀ s' ∧
        bytesAt s'.mem ((op s₀).setWidth 64) H.D =
          (hO.md.digest (hO.md.stateAt s.mem ((inn s₀).setWidth 64))).take H.D := fun t kt ht =>
    WP.mono (restore_ok H.st kt.ebp kt.saved (by rw [kt.wr]; exact sR) hL hw)
      fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => by
          by_cases he : r = .esp
          · subst he; rw [ho _ (by decide) (by decide), kt.esp]
          · exact hg r (callee_saved r hr he), by rw [hm]; exact kt.ret hp⟩, by rw [hm]; exact ht⟩
  by_cases hDN' : H.D < H.N
  · simp only [Hash.finOut, hDN', ite_true, List.append_assoc]
    refine atBlk_ok fun s₁ e₁ g₁ m₁ rd₁ wr₁ => ?_
    have k₁ : KR (H := H.st) sc s₀ s₁ := kr_write hz hp hk rd₁ wr₁ (fun r h1 _ _ => g₁ r h1) (a := 0) (n := 0)
      (by omega_using []) (by rw [m₁]; exact Frame.refl _ _)
    have aN : (inn s₀ + BitVec.ofNat 32 H.N).setWidth 64 = (inn s₀).setWidth 64 + BitVec.ofNat 64 H.N :=
      setWidth_add (by omega_using [ni, hB64])
    have tN : (inn s₀ + BitVec.ofNat 32 H.N).toNat = (inn s₀).toNat + H.N := toNat_add_ofNat (by omega_using [hB64, ni])
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega_using [ni]) (by rw [e₁, hk.ebx, tN]; omega_using [ni, hB64, hN]) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := inReg (o := 0) (n := H.N) (cov_in hz hp (s := s₀) rfl) (by omega_using []) (hz.NB_lt64)
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [e₁, hk.ebx, aN, k₁.wr]; exact inReg (cov_in hz hp (s := s₀) rfl) (by omega_using [hB64, hN]) (hz.NB_lt64)
    · rw [k₁.ebx, e₁, hk.ebx, aN]; exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hN])
    rw [e₁, hk.ebx, aN, k₁.ebx, m₁] at m₂
    have f₂ : Frame [⟨(inn s₀).setWidth 64 + BitVec.ofNat 64 H.N, H.N⟩] s₁.mem s₂.mem := by
      rw [m₂, m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    have k₂ : KR (H := H.st) sc s₀ s₂ := kr_write hz hp k₁ rd₂ wr₂ (fun r _ h2 h3 => g₂ r h2 h3) (by omega_using [hB64, hN]) f₂
    refine copyW_ok (by decide) (by decide) (H.D / 4) _ s₂ _ k₂.ebx k₂.edi (by omega_using [ni, hB64, hDN, hN]) (by omega_using [np])
      (fun j hj => by
        rw [addr_eq (by omega_using [hj, ni, hB64, hDN, hN])]; exact InRegions.right' (inReg (cov_in hz hp k₂.wr) (by omega_using [hj, hB64, hDN, hN]) (hz.NB_lt64)))
      (fun j hj => by
        rw [addr_eq (by omega_using [hj, np]), k₂.wr]; exact ⟨_, pR, Offset.contains_base _ (by omega_using [hj, eD]) (by omega_using [hj, hDN, hN])⟩) ?_
      fun s₃ g₃ rd₃ wr₃ m₃ => ?_
    · rw [hd4, BitVec.add_zero]
      exact hp.i_p.sep (by rw [inR_eq hz]; exact Offset.contains_base _ (hz.ND_le) (hz.N_lt64))
        (Region.contains_self _ _)
    rw [hd4, BitVec.add_zero] at m₃
    have f₃ : Frame [opR (H := H.st) s₀] s₂.mem s₃.mem := by
      rw [m₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    have k₃ : KR (H := H.st) sc s₀ s₃ := k₂.keep rd₃ wr₃ (fun r hr => g₃ r (by revert hr; decide +revert)) f₃
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₃ k₃ ?_
    rw [m₃, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hz.D_lt64), m₂,
      bytesAt_take _ _ (Nat.le_of_lt hDN'), bytesAt_writeBytes_self' hdl (hz.N_lt64)]
  · have e : H.D = H.N := by omega_using [hDN', hDN]
    simp only [Hash.finOut, hDN', ite_false, List.cons_append]
    refine wp_mov fun s₁ u₁ => ?_
    have k₁ : KR (H := H.st) sc s₀ s₁ := kr_write hz hp hk u₁.rd u₁.wr (fun r h1 _ _ => u₁.other r h1) (a := 0) (n := 0)
      (by omega_using []) (by rw [u₁.mem]; exact Frame.refl _ _)
    rw [WP.block_append_iff]
    refine WP.mono (hO.out s₁ (by rw [k₁.ebx]; omega_using [ni]) (by rw [u₁.gpr, hk.edi]; omega_using [hDN', np]) ?_ ?_ ?_)
      fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
    · rw [k₁.ebx, k₁.rd, k₁.wr]
      have := inReg (o := 0) (n := H.N) (cov_in hz hp (s := s₀) rfl) (by omega_using []) (hz.NB_lt64)
      rw [BitVec.add_zero] at this
      exact InRegions.right' this
    · rw [u₁.gpr, hk.edi, k₁.wr]; exact ⟨_, pR, Memory.contains_base (by omega_using [hDN', eD])⟩
    · rw [k₁.ebx, u₁.gpr, hk.edi]; exact hp.i_p.sub_left sI |>.sub_right (Region.sub_prefix (by omega_using [eD, e]))
    rw [u₁.gpr, hk.edi, k₁.ebx, u₁.mem] at m₂
    have f₂ : Frame [opR (H := H.st) s₀] s₁.mem s₂.mem := by
      rw [m₂, u₁.mem]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Memory.contains_base (by omega_using [eD, e]))
    have k₂ : KR (H := H.st) sc s₀ s₂ := k₁.keep rd₂ wr₂
      (fun r hr => g₂ r (by revert hr; decide +revert) (by revert hr; decide +revert)) f₂
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.p_s.symm.sub_left (save_sub hp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩)
    refine epi s₂ k₂ ?_
    rw [m₂, List.take_of_length_le (by omega_using [hDN', hdl]), bytesAt_take _ _ (Nat.le_of_eq e) (F := H.N),
      bytesAt_writeBytes_self' hdl (hz.N_lt64), List.take_of_length_le (by omega_using [hdl, e])]

theorem correct : WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hO.hH.SH sc).post s₀ s' := by
  have hz := hO.sizes
  obtain ⟨hb, hf, hw, hso, hW, hN0, hN, hD0, hDN, hB, hB64, hS, hDF, ni, no, np⟩ := bounds hz hp
  have hl := hO.link
  have tl := hz.tail_length; have hDL := hz.DL
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, si₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hO.hH hp k₁) fun t₁ ⟨kt₁, a₁, st₁, m₁⟩ =>
    finCall_ok hO.hH hp kt₁ a₁ fun s₂ k₂ si₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (mid_ok hO hp k₂ (by rw [si₂, st₁, si₁])) fun s₃ ⟨k₃, ax₃, e₃, b₃, p₃, f₃⟩ => ?_)
  refine WP.seq (cmpF_ok hO hp k₃ ax₃ fun s₄ k₄ f₄ e₄ => ?_)
  refine WP.mono (out_ok hO hp k₄) fun s' ⟨habi, hmac⟩ => ⟨habi, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hO.hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until it is copied.
  have oI : ∀ r ∈ [saveR H.st (scr s₀)], Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  have o₂ : ∀ r ∈ [inR (H := H.st) s₀, tR (H := H.st) s₀, calR hO.hH s₀, stkR s₀],
      Region.Disjoint (outerR (H := H.st) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (VG.Proof.Pbkdf2.Stream.X86.Finalize.cal_sub hO.hH hp)
    · exact hp.b_o.symm
  have rO₂ := Pbkdf2.Stream.X86.repr_keep hO.hH f₂ o₂ (m₁ ▸ Pbkdf2.Stream.X86.repr_keep hO.hH f₁ oI hrO)
  -- The inner digest.
  have dig := d₂ _ (m₁ ▸ Pbkdf2.Stream.X86.repr_keep hO.hH f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [show arg s₀ 3 ++ arg s₀ 2 = Pbkdf2.Stream.X86.countF s₀ from rfl, hcnt, hl0])
  rw [← bytesAt_take _ _ hDF] at dig
  -- The outer hash value.
  have lo : (xorPad k0 opad).length = H.B := by simp [xorPad, hk0]
  have so₂ : hO.md.stateAt s₂.mem ((outer s₀).setWidth 64) = hO.md.compressList hO.iv (xorPad k0 opad) 1 :=
    Md.stateAt_of_repr (hz.B_pos) lo (hl.repr _ _ _ rO₂)
  have pad₃ : bytesAt s₃.mem ((inn s₀).setWidth 64 + BitVec.ofNat 64 H.N + BitVec.ofNat 64 H.D) (H.B - H.D) =
      hO.md.tailPad H.D := by rw [Memory.add_ofNat, p₃, hO.tail]
  rw [e₄, e₃, so₂, Md.blockAt_tailPad (by omega_using [hB64, hDN, hN]) pad₃, b₃, dig] at hmac
  show bytesAt s'.mem ((op s₀).setWidth 64) hO.hH.SH.digestBytes = hmacBlockKey hO.hH.SH.H k0 text
  rw [hO.hH.hD, hmac, hl.hmac_outer (by rw [hk0]) text]

end

end VG.Proof.Pbkdf2.Md.X86.HmacFin
