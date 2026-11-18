module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
import VerifiedGarbage.Proof.Pbkdf2.MdKeys
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-! ### `Pbkdf2.Md.Arm.HmacFinCT`, which the modules that import this one used -/

section

/-! ### `Pbkdf2.Md.Arm.HmacFin`, which only this module used -/

section

/-!
# HMAC's `finalize` over a Merkle–Damgård hash function on ARMv7: correct

`finalize` (`Impl/Pbkdf2/Md/Arm.lean`) finalizes the inner state with the hash
function's streaming `finalize`, in a frame that pushes its stack arguments
(`fin_frame`, `Proof/Pbkdf2/Stream/Arm/Hash.lean`), into the block; copies the
outer state's hash value to the hash value being compressed and writes the
padding after the inner digest; compresses the block once
(`compressBlock_ok`); and writes the digest to `out`. `Md.hmac_outer` says
that this is HMAC. The contract is `finG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm.Fin

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash copyW padFrom constW lenWords)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (finG below count SavedRegs saveR savedRegs preserved_saved FinArgs fin_frame
  After below_eq)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_ldrSp op2_reg)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.Common (bytesAt_take bytesAt_writeBytes_self' sub_of_off sub_of_self)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev outer : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev scA : Addr := State.addr (scr s₀)
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev inR : Region := ⟨State.addr (inn s₀), H.N + H.B⟩
abbrev outerR : Region := ⟨State.addr (outer s₀), H.N + H.B⟩
abbrev opR : Region := ⟨State.addr (op s₀), H.D⟩
abbrev scR : Region := ⟨scA s₀, 8 * sc⟩
/-- The hash value being compressed and the block, as registers hold them. -/
abbrev hv : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.hvO
abbrev blk : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.blkO
/-- And as addresses. -/
abbrev hvA : Addr := scA s₀ + BitVec.ofNat 64 H.hvO
abbrev blkA : Addr := scA s₀ + BitVec.ofNat 64 H.blkO

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [outerR H s₀, argR s₀]
  wr : s₀.wr = [inR H s₀, opR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outerR H s₀)
  i_p : (inR H s₀).Disjoint (opR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_p : (outerR H s₀).Disjoint (opR H s₀)
  o_s : (outerR H s₀).Disjoint (scR sc s₀)
  p_s : (opR H s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR H s₀)
  a_p : (argR s₀).Disjoint (opR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_i : (below s₀).Disjoint (inR H s₀)
  b_o : (below s₀).Disjoint (outerR H s₀)
  b_p : (below s₀).Disjoint (opR H s₀)
  b_s : (below s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (outer s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  np : (op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32
  fits : H.st.buf + H.N + H.B ≤ 8 * sc

theorem pre_of {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (h : (finG hH.SH sc).pre s₀)
    (hfit : H.st.buf + H.N + H.B ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit⟩

theorem buf_eq (H : Hash) : H.st.buf = 8 * H.st.W + 36 := rfl

theorem add0 (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The parts of the scratch space -/

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

omit hz hp in
theorem scr_sub {a n : Nat} (h : a + n ≤ 8 * sc) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 a, n⟩ (scR sc s₀) :=
  Offset.sub_base _ h

omit hz in
theorem in_scr {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions s.wr (scA s₀ + BitVec.ofNat 64 a) n :=
  ⟨scR sc s₀, by simp [hwr, hp.wr], Offset.contains_base _ h (by have hp_nw := hp.nw; omega_arith)⟩

omit hz in
theorem in_scr' {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ 8 * sc) :
    InRegions (s.rd ++ s.wr) (scA s₀ + BitVec.ofNat 64 a) n := by
  obtain ⟨r, hr, hc⟩ := in_scr hp hwr h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

omit hz in
theorem addr_sO {o : Nat} (h : o < 8 * sc) :
    State.addr (scr s₀ + BitVec.ofNat 32 o) = scA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have hp_nw := hp.nw; omega_arith)

omit hz in
theorem toNat_sO {o : Nat} (h : o < 8 * sc) : (scr s₀ + BitVec.ofNat 32 o).toNat = (scr s₀).toNat + o := by
  have hp_nw := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem addr_hv : State.addr (hv H s₀) = hvA H s₀ := by
  obtain hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega_arith
  exact addr_sO hp (by simp only [Hash.hvO]; omega_arith)

theorem addr_blk : State.addr (blk H s₀) = blkA H s₀ := by
  obtain hp_fits := hp.fits; have hz_N64 := hz.N64; have : 64 ≤ H.B := by rcases hz.B with h | h <;> omega_arith
  exact addr_sO hp (by simp only [Hash.blkO]; omega_arith)

omit hz in
theorem in_blk {s : State} (hwr : s.wr = s₀.wr) {a n : Nat} (h : a + n ≤ H.B) :
    InRegions s.wr (blkA H s₀ + BitVec.ofNat 64 a) n := by
  have hp_fits := hp.fits
  rw [Memory.add_ofNat]; exact in_scr hp hwr (by simp only [Hash.blkO]; omega_arith)

omit hz in
theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  obtain hp_fits := hp.fits; rw [buf_eq H] at hp_fits; exact scr_sub (by omega_arith)

omit hz in
theorem blk_sub : Region.Sub ⟨blkA H s₀, H.B⟩ (scR sc s₀) := by
  obtain hp_fits := hp.fits; exact scr_sub (by simp only [Hash.blkO]; omega_arith)

/-- The saved registers are outside the hash value, the block and the
working space of the functions we call. -/
theorem save_disj : ∀ r ∈ [⟨scA s₀, 8 * H.st.W⟩, ⟨hvA H s₀, H.N + H.B⟩, inR H s₀, opR H s₀, below s₀],
    (saveR H.st (scr s₀)).Disjoint r := by
  obtain hz_W := hz.W; have hp_fits := hp.fits; have hp_nw := hp.nw; rw [buf_eq H] at *
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by omega_arith) (hz.buf_le64)
  · exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, buf_eq H]; omega_arith)) (hz.buf_le64)
      (by simp only [Hash.hvO, buf_eq H]; omega_arith)
  · exact (hp.i_s.sub_right (save_sub hp)).symm
  · exact (hp.p_s.sub_right (save_sub hp)).symm
  · exact (hp.b_s.sub_right (save_sub hp)).symm

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on: memory differs from
the entry's only in the regions we may write and below the stack pointer. -/
structure KR (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = outer s₀
  r7 : s.gpr .r7 = op s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame [inR H s₀, opR H s₀, scR sc s₀, below s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r7, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR H sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [inR H s₀, opR H s₀, scR sc s₀, below s₀], Region.Sub r r') : KR H sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5,
    (hg _ (by simp)).trans h.r7, (hg _ (by simp)).trans h.r11, h.saved.frame H.st hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s s' : State} (h : KR H sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR H sc s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

end

/-! ## The prologue and the call of `finalize` -/

section
variable {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hp

theorem sa1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have hp_spf := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (k := 4 * 1) (by omega_arith), addr_add (k := 4 * 0) (by omega_arith), BitVec.add_zero]

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR H s₀ ∈ s₀.wr ∧ opR H s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

include hH in
theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR H sc s₀ s ∧ s.gpr .r0 = inn s₀ ∧
    count s = count s₀ ∧ Frame [saveR H.st (scr s₀)] s₀.mem s.mem := by
  have hz := hH.sizes
  obtain hW := hz.W; have hf := hp.fits; have nw := hp.nw; rw [buf_eq H] at hf
  obtain ⟨sR, _, _⟩ := wr_mem hp
  obtain aR : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp
  unfold Hash.finPrologue
  simp only [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl
    ⟨argR s₀, aR, by rw [sa1 hp]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ => ?_
  refine Pbkdf2.Stream.Arm.save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (L := 8 * sc)
    (by omega_using [hf]) nw fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  obtain hsp₂ : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, hsp₂]; rfl)
      (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
          exact ⟨argR s₀, aR, by simp [Region.Contains]⟩) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  obtain e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  obtain f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  obtain ea : s₂.mem.readW (stackArgAddr s₀ 0) 32 = op s₀ :=
    f₂'.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.a_s.sub_left (Region.sub_prefix (by omega_arith))).sub_right (save_sub hp)) (by decide)
  obtain k : ∀ r, r ≠ .r5 → r ≠ .r7 → r ≠ .r11 → r ≠ .r12 → s₅.gpr r = s₀.gpr r :=
    fun r h5 h7 h11 h12 => by rw [u₅.other r h11, u₄.other r h7, u₃.other r h5, e₂ r h12]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, hsp₂],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, ea],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    hm ▸ f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR sc s₀, by simp, save_sub hp⟩⟩,
    k _ (by decide) (by decide) (by decide) (by decide),
    by simp only [count, k _ (by decide) (by decide) (by decide) (by decide : Reg.r2 ≠ .r12),
      k _ (by decide) (by decide) (by decide) (by decide : Reg.r3 ≠ .r12)], hm ▸ f₂'⟩

/-- The regions of the call of `finalize` on `inner`, into the block. -/
theorem finArgs {t : State} (hk : KR H sc s₀ t) (h0 : t.gpr .r0 = inn s₀)
    (h1 : t.gpr .r1 = blk H s₀) (h12 : t.gpr .r12 = scr s₀) :
    FinArgs hH.stream t (inn s₀) (blk H s₀) (scr s₀) := by
  have hz := hH.sizes
  obtain hwb := hH.stream.hWb; have hf := hp.fits; have nw := hp.nw; have hz_W := hz.W; have hz_N64 := hz.N64
  have hB := hz.B_range
  obtain eS := hz.S; have eF := hz.F
  rw [buf_eq H] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  obtain ab := addr_blk hz hp
  obtain bS : Region.Sub ⟨blkA H s₀, H.N⟩ (scR sc s₀) := fun a h => blk_sub hp a (Region.sub_prefix (by omega_using [hB, hz_N64]) a h)
  obtain cS : Region.Sub ⟨scA s₀, hH.stream.Wb⟩ (scR sc s₀) := Region.sub_prefix (by omega_arith)
  obtain cB : Region.Disjoint ⟨blkA H s₀, H.N⟩ ⟨scA s₀, hH.stream.Wb⟩ :=
    Offset.disjoint_base _ (by simp only [Hash.blkO, buf_eq H]; omega_using [hwb]) (by simp only [Hash.blkO, buf_eq H]; omega_using [nw, hf])
  exact
    { r0 := h0, r1 := h1, r12 := h12
      sp16 := by rw [hk.sp]; exact hp.sp16
      cw := by
        rw [hk.wr, ab, eS, eF]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR (by simp only [Hash.blkO, buf_eq H]; omega_arith)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.stream.Wb ≤ 8 * sc; omega_arith)
      st_o := by rw [ab, eS, eF]; exact hp.i_s.sub_right bS
      st_sc := by rw [eS]; exact hp.i_s.sub_right cS
      o_sc := by rw [ab, eF]; exact cB
      b_st := by rw [below_eq hk.sp, eS]; exact hp.b_i
      b_o := by rw [below_eq hk.sp, ab, eF]; exact hp.b_s.sub_right bS
      b_sc := by rw [below_eq hk.sp]; exact hp.b_s.sub_right cS
      nst := by rw [eS]; exact hp.ni
      no := by rw [toNat_sO hp (by simp only [Hash.blkO, buf_eq H]; omega_using [hB, hf]), eF]; simp only [Hash.blkO, buf_eq H]; omega_arith
      nsc := by omega_arith }

/-- The call's arguments: the count still in `r2:r3`. -/
theorem fin1Args_ok {s : State} (hk : KR H sc s₀ s) (h0 : s.gpr .r0 = inn s₀) :
    WP isa (.block (([] : List Instr) ++ [] ++ scrAt .r1 H.blkO ++ ([.mov .r12 (.reg .r11)] : List Instr))) s
      fun t => KR H sc s₀ t ∧ FinArgs hH.stream t (inn s₀) (blk H s₀) (scr s₀) ∧ count t = count s ∧
        t.mem = s.mem := by
  obtain hf := hp.fits; have := hH.sizes.W
  simp only [List.nil_append]
  refine scrAt_ok (by simp only [Hash.blkO, buf_eq H]; have := hH.sizes.N64; have := hH.B_le; omega_arith)
    fun s₁ g₁ d₁ m₁ rd₁ wr₁ sp₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_
  obtain k₁ : KR H sc s₀ s₁ := hk.keep rd₁ wr₁ sp₁ (fun r hr => g₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (rs := []) (by rw [m₁]; exact Frame.refl _ _) (by simp) (by simp)
  obtain k₂ : KR H sc s₀ s₂ := k₁.upd (by decide) u₂
  refine ⟨k₂, finArgs hH hp k₂ ?_ ?_ ?_, ?_, by rw [u₂.mem, m₁]⟩
  · rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), h0]
  · rw [u₂.other _ (by decide), d₁, hk.r11]
  · rw [u₂.gpr, g₁ _ (by decide) (by decide), hk.r11]
  · simp only [count, u₂.other _ (show Reg.r2 ≠ .r12 by decide), g₁ _ (show Reg.r2 ≠ .r1 by decide)
      (show Reg.r2 ≠ .r12 by decide), u₂.other _ (show Reg.r3 ≠ .r12 by decide),
      g₁ _ (show Reg.r3 ≠ .r1 by decide) (show Reg.r3 ≠ .r12 by decide)]

theorem finCall_ok {t : State} (hk : KR H sc s₀ t) (ha : FinArgs hH.stream t (inn s₀) (blk H s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' →
      Frame [inR H s₀, ⟨blkA H s₀, H.N⟩, ⟨scA s₀, hH.stream.Wb⟩, below s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (State.addr (inn s₀)) m → m.length < 2 ^ 64 → count t = BitVec.ofNat 64 m.length →
        bytesAt s'.mem (blkA H s₀) H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push Pbkdf2.Stream.Arm.fin2) (.call H.st.finN H.st.finC) (.pop .r1 8)) t Q :=
  fin_frame hH.stream ha fun s' ha' hpost => by
    have hz := hH.sizes
    obtain hz_W := hz.W; have := hH.stream.hWb; have hz_DN := hz.DN; have hz_NL := hz.NL; have hfi := hp.fits
    rw [buf_eq H] at hfi
    obtain ab := addr_blk hz hp
    have f := ha'.frame
    rw [below_eq hk.sp, ab, hz.S, hz.F] at f
    rw [ab, hz.F] at hpost
    obtain cS : Region.Sub ⟨scA s₀, hH.stream.Wb⟩ ⟨scA s₀, 8 * H.st.W⟩ := Region.sub_prefix (by omega_arith)
    obtain sd := save_disj hz hp
    refine hQ s' (hk.keep ha'.rd ha'.wr ha'.sp (fun r hr => ha'.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
      ?_ ?_) f fun m hr hl hc => ?_
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r ((rfl | rfl | rfl) | rfl)
      · exact sd _ (by simp)
      · exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right
          (Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega_arith) (by simp only [Hash.hvO, Hash.blkO]; omega_arith))
      · exact (sd _ (by simp)).sub_right cS
      · exact sd _ (by simp)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r ((rfl | rfl | rfl) | rfl)
      · exact ⟨inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨scR sc s₀, by simp, fun a h => blk_sub hp a (Region.sub_prefix (by omega_arith) a h)⟩
      · exact ⟨scR sc s₀, by simp, Region.sub_prefix (by have hp_fits := hp.fits; rw [buf_eq H] at hp_fits; omega_arith)⟩
      · exact ⟨below s₀, by simp, fun _ h => h⟩
    · rw [bytesAt_take _ _ hz.DN]; exact hpost m hr hl hc

end

/-! ## The outer hash value and the padding -/

/-- The registers during the outer hash. -/
structure KR' (H : Hash) (sc : Nat) (s₀ s : State) : Prop extends KR H sc s₀ s where
  r0 : s.gpr .r0 = hv H s₀
  r3 : s.gpr .r3 = scr s₀
  r6 : s.gpr .r6 = blk H s₀

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

omit hz in
/-- What the outer hash writes: the hash value being compressed and the block. -/
theorem hb_sub : Region.Sub ⟨hvA H s₀, H.N + H.B⟩ (scR sc s₀) := by
  obtain hp_fits := hp.fits; exact scr_sub (by simp only [Hash.hvO]; omega_arith)

theorem hb_kr : ∀ r ∈ [(⟨hvA H s₀, H.N + H.B⟩ : Region)], (saveR H.st (scr s₀)).Disjoint r ∧
    ∃ r' ∈ [inR H s₀, opR H s₀, scR sc s₀, below s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨save_disj hz hp _ (by simp), scR sc s₀, by simp, hb_sub hp⟩

theorem mid_ok {md : Md H.B H.N H.L} (hR : md.Reloc)
    (hlen : wordsBytes (lenWords H.be H.L (H.B + H.D)) = md.lenBytes (H.B + H.D)) {s : State}
    (hk : KR H sc s₀ s) :
    WP isa (.block H.finMid) s fun s' => KR' H sc s₀ s' ∧ Frame [⟨hvA H s₀, H.N + H.B⟩] s.mem s'.mem ∧
      md.stateAt s'.mem (hvA H s₀) = md.stateAt s₀.mem (State.addr (outer s₀)) ∧
      bytesAt s'.mem (blkA H s₀) H.D = bytesAt s.mem (blkA H s₀) H.D ∧
      bytesAt s'.mem (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.D) = md.tailPad H.D := by
  obtain hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_pad := hz.pad; have hz_NL := hz.NL; have hz_D4 := hz.D4; have hz_L4 := hz.L4
  obtain hz_L16 := hz.L16; have hp_nw := hp.nw; have hp_no := hp.no; have hz_W := hz.W; have hz_N4 := hz.N4
  have hB := hz.B_range
  have hB4 := hz.B4
  obtain hn : 4 * (H.N / 4) = H.N := by omega_using [hz_N4]
  obtain ablk := addr_blk hz hp; have ahv := addr_hv hz hp
  obtain tb : (blk H s₀).toNat = (scr s₀).toNat + H.blkO := toNat_sO hp (by simp only [Hash.blkO]; omega_using [hz_pad, hp_fits])
  obtain th : (hv H s₀).toNat = (scr s₀).toNat + H.hvO := toNat_sO hp (by simp only [Hash.hvO]; omega_using [hz_pad, hp_fits])
  obtain ⟨sR, _, _⟩ := wr_mem hp
  unfold Hash.finMid Hash.pad Hash.atHv
  simp only [List.append_assoc, List.singleton_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  refine scrAt_ok (by simp only [Hash.hvO, buf_eq H]; omega_using [hz_W]) fun s₂ g₂ d₂ m₂ rd₂ wr₂ sp₂ =>
    scrAt_ok (by simp only [Hash.blkO, buf_eq H]; omega_using [hz_W, hz_N64]) fun s₃ g₃ d₃ m₃ rd₃ wr₃ sp₃ => ?_
  obtain r11₁ : s₁.gpr .r11 = scr s₀ := by rw [u₁.other _ (by decide), hk.r11]
  obtain r0₃ : s₃.gpr .r0 = hv H s₀ := by rw [g₃ _ (by decide) (by decide), d₂, r11₁]
  obtain r6₃ : s₃.gpr .r6 = blk H s₀ := by rw [d₃, g₂ _ (by decide) (by decide), r11₁]
  obtain r5₃ : s₃.gpr .r5 = outer s₀ := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide), u₁.other _ (by decide), hk.r5]
  obtain k₃ : KR H sc s₀ s₃ := (hk.upd (by decide) u₁).keep (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])
    (by rw [sp₃, sp₂]) (fun r hr => by
      have : r ≠ .r0 ∧ r ≠ .r6 ∧ r ≠ .r12 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [g₃ r this.2.1 this.2.2, g₂ r this.1 this.2.2]) (rs := []) (by rw [m₃, m₂]; exact Frame.refl _ _)
      (by simp) (by simp)
  obtain oR : outerR H s₀ ∈ s₃.rd ++ s₃.wr := by rw [k₃.rd, hp.rd]; simp
  refine copyW_ok (by decide) (by decide) 0 0 (H.N / 4) ⟨by omega_using [hz_N64], by omega_arith⟩ _ s₃ _
    (by rw [r5₃]; omega_using [hp_no]) (by rw [r0₃, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits])
    (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₄ g₄ rd₄ wr₄ sp₄ m₄ => ?_
  · rw [r5₃, add0]; exact ⟨outerR H s₀, oR, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hz_N64])⟩
  · rw [r0₃, ahv, k₃.wr, add0, show hvA H s₀ = scA s₀ + BitVec.ofNat 64 H.hvO from rfl, Memory.add_ofNat]
    exact in_scr hp rfl (by simp only [Hash.hvO]; omega_using [hj, hp_fits])
  · rw [r5₃, r0₃, ahv, add0, add0, hn]
    exact hp.o_s.sep (Memory.contains_base (Nat.le_add_right _ _)) (Offset.contains_base _ (by simp only [Hash.hvO]; omega_using [hp_fits])
      (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]))
  rw [r0₃, ahv, r5₃, add0, add0, hn] at m₄
  obtain g6 : s₄.gpr .r6 = blk H s₀ := by rw [g₄ _ (by decide), r6₃]
  refine padFrom_ok (a := H.D) (b := H.B - H.L) (by omega_arith) (by omega_using [hB4, hz_L4, hz_D4]) (by omega_using [hB]) (s := s₄) (p := blk H s₀) g6
    (by rw [tb]; simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
    (fun j hj => by rw [ablk]; exact in_blk hp (wr₄.trans k₃.wr) (by omega_using [hj])) fun s₅ g₅ rd₅ wr₅ sp₅ m₅ => ?_
  rw [ablk] at m₅
  obtain lw := HashOK.lenWords_length (H := H)
  rw [← List.append_nil (constW (H.B - H.L) (lenWords H.be H.L (H.B + H.D)))]
  refine constW_ok (p := blk H s₀) (lenWords H.be H.L (H.B + H.D)) (H.B - H.L) (by rw [lw]; omega_using [hB, hz_pad])
    (by rw [lw, tb]; simp only [Hash.blkO]; omega_using [hp_nw, hz_pad, hp_fits]) _ s₅ _ (by rw [g₅ _ (by decide), g6])
    (fun j hj => by rw [lw] at hj; rw [ablk]; exact in_blk hp (wr₅.trans (wr₄.trans k₃.wr)) (by omega_using [hj, hz_pad]))
    fun s₆ g₆ rd₆ wr₆ sp₆ m₆ => WP.block_nil ?_
  rw [ablk, hlen] at m₆
  obtain lpz : ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0 : List Byte).length = H.B - H.L - H.D := by
    simp; omega_using [hz_pad]
  obtain hM : s₆.mem = writeBytes (writeBytes (writeBytes s₃.mem (hvA H s₀) (bytesAt s₃.mem (State.addr (outer s₀)) H.N))
      (blkA H s₀ + BitVec.ofNat 64 H.D) ([0x80] ++ List.replicate (H.B - H.L - H.D - 1) 0))
      (blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) (md.lenBytes (H.B + H.D)) := by
    rw [m₆, m₅, m₄]
  obtain hG : ∀ r, r ≠ .r12 → s₆.gpr r = s₃.gpr r := fun r hr => by rw [g₆ r hr, g₅ r hr, g₄ r hr]
  obtain eb : blkA H s₀ = hvA H s₀ + BitVec.ofNat 64 H.N := by
    rw [hvA, blkA, Memory.add_ofNat]; rfl
  obtain fM : Frame [⟨hvA H s₀, H.N + H.B⟩] s₃.mem s₆.mem := by
    rw [hM]
    refine ((writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)).trans (writeBytes_frame _ _ _ ?_)
    · rw [bytesAt_length]; exact Memory.contains_base (Nat.le_add_right _ _)
    · rw [lpz, eb, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hz_DN, hz_N64])
    · rw [md.lenBytes_length, eb, Memory.add_ofNat]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hp_nw, hp_fits])
  obtain m₃' : s₃.mem = s.mem := by rw [m₃, m₂, u₁.mem]
  obtain S1 : Mem.Sep (blkA H s₀) H.D (blkA H s₀ + BitVec.ofNat 64 H.D) (H.B - H.L - H.D) := by
    have := Offset.sep (blkA H s₀) (d := 0) (n := H.D) (e := H.D) (k := H.B - H.L - H.D) (.inl (by omega_arith))
      (by omega_using [hz_DN, hz_N64]) (by omega_using [hp_nw, hz_DN, hp_fits])
    rwa [add0] at this
  obtain S2 : ∀ {a n : Nat}, a + n ≤ H.B - H.L →
      Mem.Sep (blkA H s₀ + BitVec.ofNat 64 a) n (blkA H s₀ + BitVec.ofNat 64 (H.B - H.L)) H.L :=
    fun h' => Offset.sep _ (.inl h') (by omega_using [h', hp_nw, hp_fits]) (by omega_using [hp_nw, hz_pad, hp_fits])
  obtain S3 : Mem.Sep (blkA H s₀) H.D (hvA H s₀) H.N := by
    have := Offset.sep (hvA H s₀) (d := H.N) (n := H.D) (e := 0) (k := H.N) (.inr (by omega_arith)) (by omega_using [hz_DN, hz_N64]) (by omega_using [hz_N64])
    rwa [add0, ← eb] at this
  obtain f₄₆ : Frame [⟨blkA H s₀, H.B⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅]
    refine (writeBytes_frame _ _ _ ?_).trans (writeBytes_frame _ _ _ ?_)
    · rw [lpz]; exact Offset.contains_base _ (by omega_using [hz_pad]) (hz.D_lt64)
    · rw [md.lenBytes_length]; exact Offset.contains_base _ (by omega_using [hz_pad]) (by omega_using [hp_nw, hp_fits])
  obtain dHB : Region.Disjoint ⟨hvA H s₀, H.N⟩ ⟨blkA H s₀, H.B⟩ :=
    Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega_arith)) (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits])
      (by simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
  refine ⟨⟨k₃.keep (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄]) (by rw [sp₆, sp₅, sp₄]) (fun r hr => hG r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
      fM (fun r hr => (hb_kr hz hp r hr).1) (fun r hr => (hb_kr hz hp r hr).2),
    by rw [hG _ (by decide), r0₃], by rw [hG _ (by decide), g₃ _ (by decide) (by decide),
      g₂ _ (by decide) (by decide), u₁.gpr, hk.r11], by rw [hG _ (by decide), r6₃]⟩,
    m₃' ▸ fM, ?_, ?_, ?_⟩
  · refine hR _ _ _ _ fun i hi => ?_
    rw [f₄₆.bytes (R := ⟨hvA H s₀, H.N⟩) (fun r hr => by simp at hr; subst hr; exact dHB) (by show H.N ≤ 2 ^ 64; omega_using [hz_N64]) hi, m₄,
      writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega_using [hz_N64]),
      bytesAt_getD' _ _ hi]
    exact k₃.frame.bytes (R := outerR H s₀) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.i_o.symm
      · exact hp.o_p
      · exact hp.o_s
      · exact hp.b_o.symm) (by show H.N + H.B ≤ 2 ^ 64; omega_using [hp_nw, hp_fits]) (by show i < H.N + H.B; omega_using [hi])
  · rw [hM, bytesAt_writeBytes_sep _ _ (by
        rw [md.lenBytes_length]; have := S2 (a := 0) (n := H.D) (by omega_using [hz_pad]); rwa [add0] at this) (hz.D_lt64),
      bytesAt_writeBytes_sep _ _ (by rw [lpz]; exact S1) (hz.D_lt64),
      bytesAt_writeBytes_sep _ _ (by rw [bytesAt_length]; exact S3) (hz.D_lt64), m₃']
  · rw [show H.B - H.D = (H.B - H.L - H.D) + H.L by omega_using [hz_pad], bytesAt_add, Memory.add_ofNat (blkA H s₀),
      show H.D + (H.B - H.L - H.D) = H.B - H.L by omega_using [hz_pad], hM,
      bytesAt_writeBytes_self' (md.lenBytes_length _) (by omega_using [hz_L16]),
      bytesAt_writeBytes_sep _ _ (by rw [md.lenBytes_length]; exact S2 (by omega_using [hz_pad])) (hz.BLD_lt64),
      bytesAt_writeBytes_self' lpz (hz.BLD_lt64), Md.tailPad, show H.B - H.L - 1 - H.D = H.B - H.L - H.D - 1 by omega_using []]

end

/-! ## The compression and the MAC -/

section
variable {H : Hash} {sc : Nat} (hz : Sizes H) {s₀ : State} (hp : Pre H sc s₀)
include hz hp

/-- What the call of the compression function needs. -/
theorem callOk_of {s : State} (h : KR' H sc s₀ s) :
    CallOk s H.N H.B H.so (hv H s₀) (scr s₀) (blk H s₀) := by
  obtain hz_N64 := hz.N64; have hp_fits := hp.fits; have hp_nw := hp.nw; have hz_so := hz.so; have hB := hz.B
  obtain hsc : scR sc s₀ ∈ s.wr := by simp [h.wr, hp.wr]
  rw [buf_eq H] at *
  refine ⟨h.r0, h.r3, h.r6, by rw [toNat_sO hp (by simp only [Hash.hvO, buf_eq H]; omega_arith)]; simp only [Hash.hvO, buf_eq H]; omega_arith,
    by rw [toNat_sO hp (by simp only [Hash.blkO, buf_eq H]; omega_arith)]; simp only [Hash.blkO, buf_eq H]; omega_arith,
    by omega_arith, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [addr_hv hz hp, addr_blk hz hp, hvA, blkA, Hash.hvO, Hash.blkO, buf_eq H]
  · exact Offset.disjoint_base _ (by omega_arith) (hz.bufN_le64)
  · exact Offset.disjoint _ (.inr (by omega_arith)) (hz.bufNB_le64) (hz.bufN_le64)
  · exact Offset.disjoint_base _ (by omega_arith) (hz.bufNB_le64)
  · refine Covers.of_sub fun r hr => ⟨scR sc s₀, List.mem_append_right _ hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨0, by simp, by dsimp only; omega_arith⟩
  · refine Covers.of_sub fun r hr => ⟨scR sc s₀, hsc, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, rfl, by dsimp only; omega_arith⟩
    · exact ⟨0, by simp, by dsimp only; omega_arith⟩

/-- The compression of the block into the outer hash value. -/
theorem cmp_ok {md : Md H.B H.N H.L} (hf : CompOk md H.so H.compC) {s : State} (h : KR' H sc s₀ s)
    {Q : State → Prop}
    (k : ∀ s', KR' H sc s₀ s' → Frame [⟨hvA H s₀, H.N⟩, ⟨scA s₀, H.so⟩] s.mem s'.mem →
      md.stateAt s'.mem (hvA H s₀) = md.compress (md.stateAt s.mem (hvA H s₀)) (md.blockAt s.mem (blkA H s₀)) →
      Q s') :
    WP isa H.compressBlock s Q := by
  obtain hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_so := hz.so; have hz_W := hz.W
  have hB := hz.B_range
  refine compressBlock_ok hf (callOk_of hz hp h) fun s' hrd hwr hcs h0 h3 hsp hfr hst => ?_
  rw [addr_hv hz hp] at hfr
  rw [addr_hv hz hp, addr_blk hz hp] at hst
  obtain sd := save_disj hz hp
  rw [buf_eq H] at *
  refine k s' ⟨h.toKR.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hfr ?_ ?_,
    h0, h3, (hcs _ (by decide) (by decide)).trans h.r6⟩ hfr hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right (Region.sub_prefix (Nat.le_add_right _ _))
    · exact (sd ⟨scA s₀, 8 * H.st.W⟩ (List.mem_cons_self ..)).sub_right (Region.sub_prefix (by omega_arith))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact ⟨scR sc s₀, by simp, scr_sub (by simp only [Hash.hvO, buf_eq H]; omega_arith)⟩
    · exact ⟨scR sc s₀, by simp, Region.sub_prefix (by omega_arith)⟩

/-- The MAC to `out`, and our caller's registers back. -/
theorem out_ok {md : Md H.B H.N H.L} (ho : OutOk md H.out) {s : State} (h : KR' H sc s₀ s) :
    WP isa (.block H.finOut) s fun s' => abiPreserved s₀ s' ∧
      bytesAt s'.mem (State.addr (op s₀)) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D := by
  obtain hz_N64 := hz.N64; have hp_fits := hp.fits; have hz_DN := hz.DN; have hz_D4 := hz.D4; have hz_W := hz.W; have hp_nw := hp.nw; have hp_np := hp.np
  have hB := hz.B_range
  obtain hD4 : 4 * (H.D / 4) = H.D := by omega_arith
  obtain ahv := addr_hv hz hp; have ablk := addr_blk hz hp
  obtain th : (hv H s₀).toNat = (scr s₀).toNat + H.hvO := toNat_sO hp (by simp only [Hash.hvO]; omega_arith)
  obtain tb : (blk H s₀).toNat = (scr s₀).toNat + H.blkO := toNat_sO hp (by simp only [Hash.blkO]; omega_arith)
  obtain ⟨sR, _, pR⟩ := wr_mem hp
  obtain hdl := md.digest_length (md.stateAt s.mem (hvA H s₀))
  -- The restore, after code that writes `out` and maybe the block.
  obtain fin : ∀ s₁ : State, s₁.gpr .r11 = scr s₀ → s₁.rd = s.rd → s₁.wr = s.wr → s₁.sp = s.sp →
      SavedRegs H.st (scr s₀) s₀ s₁.mem →
      bytesAt s₁.mem (State.addr (op s₀)) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D →
      WP isa (.block H.st.restore) s₁ fun s' => abiPreserved s₀ s' ∧
        bytesAt s'.mem (State.addr (op s₀)) H.D = (md.digest (md.stateAt s.mem (hvA H s₀))).take H.D := by
    intro s₁ h11 hrd hwr hsp hsv hb
    obtain hfi := hp.fits; rw [buf_eq H] at hfi
    exact WP.mono (Pbkdf2.Stream.Arm.restore_ok H.st h11 hz.W hsv (by rw [hwr, h.wr, hp.wr]; simp) (L := 8 * sc)
      (by omega_using [hfi]) hp.nw) fun s' ⟨hm, _, _, hsp', hg, _⟩ =>
        ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp', hsp, h.sp]⟩, by rw [hm]; exact hb⟩
  obtain sdisj : ∀ {R : Region}, R ∈ [opR H s₀, ⟨blkA H s₀, H.N⟩] → (saveR H.st (scr s₀)).Disjoint R := by
    intro R hR
    obtain sd := save_disj hz hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact sd _ (by simp)
    · have hfi := hp.fits; rw [buf_eq H] at hfi
      exact (sd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).sub_right
        (Offset.sub _ (by simp only [Hash.hvO, Hash.blkO]; omega_using []) (by simp only [Hash.hvO, Hash.blkO]; omega_using [hB, hz_N64]))
  unfold Hash.finOut
  by_cases hDN : H.D < H.N
  · simp only [hDN, ↓reduceIte, List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (ho s ?_ ?_ ?_ ?_ ?_) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, m₁⟩ => ?_
    · rw [h.r0, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]
    · rw [h.r6, tb]; simp only [Hash.blkO]; omega_using [hB, hp_nw, hp_fits, hz_N64]
    · rw [h.r0, ahv]; exact in_scr' hp h.wr (by simp only [Hash.hvO]; omega_using [hp_fits])
    · rw [h.r6, ablk]; exact in_scr hp h.wr (by simp only [Hash.blkO]; omega_using [hB, hp_fits, hz_N64])
    · rw [h.r0, h.r6, ahv, ablk]; exact Offset.disjoint _ (.inl (by simp only [Hash.hvO, Hash.blkO]; omega_arith))
        (by simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]) (by simp only [Hash.blkO]; omega_using [hp_nw, hp_fits])
    rw [h.r6, ablk, h.r0, ahv] at m₁
    obtain g6 : s₁.gpr .r6 = blk H s₀ := by rw [g₁ _ (by decide) (by decide), h.r6]
    obtain g7 : s₁.gpr .r7 = op s₀ := by rw [g₁ _ (by decide) (by decide), h.r7]
    refine copyW_ok (by decide) (by decide) 0 0 (H.D / 4) ⟨by omega_using [hz_DN, hz_N64], by omega_arith⟩ _ s₁ _
      (by rw [g6, tb]; simp only [Hash.blkO]; omega_arith) (by rw [g7]; omega_arith)
      (fun j hj => ?_) (fun j hj => ?_) ?_ fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
    · rw [g6, ablk, rd₁, wr₁, add0]
      obtain ⟨r, hr, hc⟩ := in_blk hp h.wr (a := 4 * j) (n := 4) (by omega_using [hj, hB, hz_DN, hz_N64])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [g7, wr₁, h.wr, add0]; exact ⟨opR H s₀, pR, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hz_DN, hz_N64])⟩
    · rw [g6, g7, ablk, add0, add0, hD4]
      exact (hp.p_s.sub_right (fun a ha => blk_sub hp a (Region.sub_prefix (by omega_using [hB, hz_DN, hz_N64]) a ha))).symm.sep
        (Region.contains_self _ _) (Region.contains_self _ _)
    rw [g7, g6, ablk, add0, add0, hD4] at m₂
    obtain f₁ : Frame [⟨blkA H s₀, H.N⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hdl]; exact Region.contains_self _ _)
    obtain f₂ : Frame [opR H s₀] s₁.mem s₂.mem := by
      rw [m₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
    refine fin s₂ (by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide), h.r11]) (rd₂.trans rd₁)
      (wr₂.trans wr₁) (sp₂.trans sp₁) ((h.saved.frame H.st f₁ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)).frame H.st f₂ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)) ?_
    rw [m₂, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (hz.D_lt64), bytesAt_take _ _ hz.DN, m₁,
      bytesAt_writeBytes_self' hdl (hz.N_lt64)]
  · simp only [hDN, ↓reduceIte, List.cons_append]
    obtain eDN : H.D = H.N := by omega_using [hDN, hz_DN]
    refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (ho s₁ ?_ ?_ ?_ ?_ ?_) fun s₂ ⟨g₂, rd₂, wr₂, sp₂, m₂⟩ => ?_
    · rw [u₁.other _ (by decide), h.r0, th]; simp only [Hash.hvO]; omega_using [hp_nw, hp_fits]
    · rw [u₁.gpr, h.r7, ← eDN]; omega_arith
    · rw [u₁.other _ (by decide), h.r0, ahv, u₁.rd, u₁.wr]; exact in_scr' hp h.wr (by simp only [Hash.hvO]; omega_using [hp_fits])
    · rw [u₁.gpr, h.r7, u₁.wr, h.wr, ← eDN]; exact ⟨opR H s₀, pR, Region.contains_self _ _⟩
    · rw [u₁.other _ (by decide), u₁.gpr, h.r0, h.r7, ahv, ← eDN]
      exact (hp.p_s.sub_right (scr_sub (by simp only [Hash.hvO]; omega_using [hz_DN, hp_fits]))).symm
    rw [u₁.gpr, h.r7, u₁.other _ (by decide), h.r0, ahv, u₁.mem] at m₂
    obtain f₂ : Frame [opR H s₀] s.mem s₂.mem := by
      rw [m₂]; exact writeBytes_frame _ _ _ (by rw [hdl, ← eDN]; exact Region.contains_self _ _)
    refine fin s₂ (by rw [g₂ _ (by decide) (by decide), u₁.other _ (by decide), h.r11]) (rd₂.trans u₁.rd)
      (wr₂.trans u₁.wr) (sp₂.trans u₁.sp) (h.saved.frame H.st f₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact sdisj (by simp)) ?_
    rw [m₂, eDN, bytesAt_writeBytes_self' hdl (hz.N_lt64), List.take_of_length_le (by rw [hdl])]

end

/-! ## Correctness -/

theorem correct {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀) :
    WP isa H.hmacFin s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  have hz := hH.sizes
  obtain hz_N64 := hz.N64; have hz_DN := hz.DN; have hz_NL := hz.NL; have hp_fits := hp.fits
  have hB := hz.B_range
  unfold Hash.hmacFin Impl.Pbkdf2.Stream.Arm.Hash.callFin
  refine WP.seq (WP.mono (pro_ok hH hp) fun s₁ ⟨k₁, r0₁, c₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH hp k₁ r0₁) fun t₁ ⟨kt₁, a₁, ct₁, mt₁⟩ =>
    finCall_ok hH hp kt₁ a₁ fun s₂ k₂ _ d₂ => ?_))
  refine WP.seq (WP.mono (mid_ok hz hp hH.reloc hH.len k₂) fun s₃ ⟨k₃, _, st₃, b₃, p₃⟩ => ?_)
  refine WP.seq (cmp_ok hz hp hH.comp k₃ fun s₄ k₄ _ e₄ => ?_)
  refine WP.mono (out_ok hz hp hH.out k₄) fun s' ⟨habi, hout⟩ => ⟨habi, ?_⟩
  intro k0 text hk0 hlen hrI hcnt hrO
  obtain hk0' : k0.length = H.B := by rw [hk0, hH.hB]
  obtain hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, VG.Proof.Hmac.Common.xorPad_length, hk0']
  -- The inner digest.
  obtain rI : hH.SH.Repr t₁.mem (State.addr (inn s₀)) (xorPad k0 ipad ++ text) := by
    rw [mt₁]
    refine Pbkdf2.Stream.Arm.repr_keep hH.stream f₁ (fun r hr => ?_) hrI
    simp only [List.mem_singleton] at hr; subst hr
    rw [hz.S]; exact (save_disj hz hp _ (by simp)).symm
  obtain dig := d₂ _ rI (by rw [hl0]; rw [hk0'] at hlen; exact hlen) (by rw [ct₁, c₁, hcnt, hl0, hH.hB])
  -- The outer hash.
  rw [st₃, blockAt_eq (by omega_using [hz_NL, hz_DN]) p₃, b₃, dig] at e₄
  show bytesAt s'.mem (State.addr (op s₀)) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hH.hD, hout, e₄, Md.hmac_outer hH.link hk0 hrO]

end VG.Proof.Pbkdf2.Md.Arm.Fin

end

end


/-!
# HMAC's `finalize` over a Merkle–Damgård hash function on ARMv7: constant time

As for `iterate` (`IterateCT.lean`): we relate two runs (`RelCT`). Correctness
determines our registers from the public arguments alone, so the taint
analysis proves the blocks between the calls constant time from them
(`Checks`, evaluated for each hash function); the call of the streaming
`finalize` is constant time by its own proof (`fin_rel`,
`Proof/Pbkdf2/Stream/Arm/Hash.lean`), and the call of the compression function
by its own (`compressBlock_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm.Fin

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (finG count FinArgs fin_rel)

/-- The registers the blocks after the outer hash value is set up use. -/
abbrev regsO : List Reg := [.r0, .r3, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `finalize` between its calls, which
depend on the hash function's sizes, its length field and its digest. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block H.finPrologue) hc).isSome = true
  fin1 : ∃ hc, (taint.check (Taint.ofRegs kregs)
    (.block (([] : List Instr) ++ [] ++ scrAt .r1 H.blkO ++ [.mov .r12 (.reg .r11)])) hc).isSome = true
  mid : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.finMid) hc).isSome = true
  out : ∃ hc, (taint.check (Taint.ofRegs regsO) (.block H.finOut) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0
  a1 : stackArg s₀ 1 = stackArg s₀' 1

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR H sc s₀ s) (h' : KR H sc s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, outer, outer, hq.r1]
  · rw [h.r7, h'.r7, op, op, hq.a0]
  · rw [h.r11, h'.r11, scr, scr, hq.a1]

theorem kr'_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR' H sc s₀ s) (h' : KR' H sc s₀' s') :
    ∀ r ∈ regsO, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r0, h'.r0, hv, hv, scr, scr, hq.a1]
  · rw [h.r3, h'.r3, scr, scr, hq.a1]
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)
  · rw [h.r6, h'.r6, blk, blk, scr, scr, hq.a1]
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)
  · exact kr_agree hq h.toKR h'.toKR _ (by simp)

/-- Code the taint analysis checks from the registers `rs`, in two runs
whose single-run facts `F` and `F'` agree on them. -/
theorem rel_regs {F F' G G' : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun s s' h => Taint.agree_ofRegs (hag s s' h.1 h.2)) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

end

theorem fin_ct {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀)
    (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacFin fun _ _ => True := by
  have hz := hH.sizes
  obtain e : inn s₀' = inn s₀ ∧ blk H s₀' = blk H s₀ ∧ scr s₀' = scr s₀ ∧ hv H s₀' = hv H s₀ := by
    refine ⟨hq.r0.symm, ?_, hq.a1.symm, ?_⟩ <;> simp only [blk, hv, scr, hq.a1]
  obtain hcnt : count s₀ = count s₀' := by rw [count, count, hq.r2, hq.r3]
  obtain aw : ∀ {t : State}, Pre H sc t →
      t.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 8⟩ r := fun {t} h => by
    obtain e : (⟨State.addr t.sp, 8⟩ : Region) = argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_p
    · exact h.a_s
  let P₁ : State → State → Prop := fun t₀ s => KR H sc t₀ s ∧ s.gpr .r0 = inn t₀ ∧ count s = count t₀
  let F₁ : State → State → Prop := fun t₀ s =>
    KR H sc t₀ s ∧ FinArgs hH.stream s (inn t₀) (blk H t₀) (scr t₀) ∧ count s = count t₀
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.finPrologue) fun s s' => P₁ s₀ s ∧ P₁ s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 8) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 2) hq.sp hp.spf fun i hi => by
            rcases (show i = 0 ∨ i = 1 by omega_using [hi]) with rfl | rfl
            · exact hq.a0
            · exact hq.a1)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hH hp) fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
      (fun _ e => by rw [e]; exact WP.mono (pro_ok hH hp') fun _ ⟨k, r0, c, _⟩ => ⟨k, r0, c⟩)
  obtain f1 := rel_regs (F := P₁ s₀) (F' := P₁ s₀') (G := F₁ s₀) (G' := F₁ s₀') kregs
    (fun _ _ h h' => kr_agree hq h.1 h'.1) hc.fin1
    (fun _ ⟨k, r0, c⟩ => WP.mono (fin1Args_ok hH hp k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
    (fun _ ⟨k, r0, c⟩ => WP.mono (fin1Args_ok hH hp' k r0) fun _ ⟨k, a, c', _⟩ => ⟨k, a, c'.trans c⟩)
  obtain call : RelCT isa (fun s s' => F₁ s₀ s ∧ F₁ s₀' s')
      (.frame (.push Pbkdf2.Stream.Arm.fin2) (.call H.st.finN H.st.finC) (.pop .r1 8))
      fun s s' => KR H sc s₀ s ∧ KR H sc s₀' s' :=
    rel_wp (fin_rel hH.stream (sp := s₀.sp) (st := inn s₀) (o := blk H s₀) (sc := scr s₀) fun s s' ⟨h, h'⟩ =>
      ⟨h.2.1, by rw [← e.1, ← e.2.1, ← e.2.2.1]; exact h'.2.1, by rw [h.2.2, h'.2.2, hcnt], h.1.sp,
        by rw [h'.1.sp, hq.sp]⟩)
      (fun _ h => finCall_ok hH hp h.1 h.2.1 fun _ k _ _ => k)
      (fun _ h => finCall_ok hH hp' h.1 h.2.1 fun _ k _ _ => k)
  obtain mid := rel_regs (F := KR H sc s₀) (F' := KR H sc s₀') (G := KR' H sc s₀) (G' := KR' H sc s₀') kregs
    (fun _ _ h h' => kr_agree hq h h') hc.mid
    (fun _ h => WP.mono (mid_ok hz hp hH.reloc hH.len h) fun _ h => h.1)
    (fun _ h => WP.mono (mid_ok hz hp' hH.reloc hH.len h) fun _ h => h.1)
  obtain cmp : RelCT isa (fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s') H.compressBlock
      fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s' :=
    rel_wp (compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := hv H s₀) (scr := scr s₀)
      (src := blk H s₀) fun s s' ⟨h, h'⟩ => by
        obtain c' := callOk_of hz hp' h'
        rw [e.2.2.2, e.2.2.1, e.2.1] at c'
        exact ⟨callOk_of hz hp h, c'⟩)
      (fun _ h => cmp_ok hz hp hH.comp h fun _ k _ _ => k)
      (fun _ h => cmp_ok hz hp' hH.comp h fun _ k _ _ => k)
  obtain ⟨_, ho⟩ := hc.out
  obtain out : RelCT isa (fun s s' => KR' H sc s₀ s ∧ KR' H sc s₀' s') (.block H.finOut) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs regsO) (fun _ _ h => Taint.agree_ofRegs (kr'_agree hq h.1 h.2)) ho
  unfold Hash.hmacFin Impl.Pbkdf2.Stream.Arm.Hash.callFin
  exact pro.seq ((f1.seq call).seq (mid.seq (cmp.seq out)))

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (finG S W).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- HMAC's `finalize` is verified against `finG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} (hfit : H.st.buf + H.N + H.B ≤ 8 * sc)
    (hsat : ∃ s, (finG hH.SH sc).pre s) :
    Verified Arm.target H.hmacFin (finG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (fin_ct hH hc (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) (pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.Fin

end

end

/-! ### `Pbkdf2.Md.Arm.HmacInit`, which only this module used -/

section

/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: correct

As on x86 (`Proof/Pbkdf2/Md/X86/HmacInit.lean`): HMAC's `init`
(`Impl/Pbkdf2/Md/Arm.lean`) saves our caller's registers (`pro_ok`), calls
the streaming `init` on both states (`callInit_ok`), writes `ipad` in every
byte of the inner state's buffer (`fill_ok`) and the key XORed into its
start (`keys_ok`), the outer buffer from the inner one, word by word
(`opad_ok`), and compresses each buffer into its state's hash value
(`compressBlock_ok`): each state then represents its block
(`Md.repr_block`). The contract is `initG`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`), the shared one's at 16 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_mov wp_add wp_ldr wp_str wp_ldrb wp_strb wp_subs wp_cmp op2_imm
  op2_reg eval_eq)
open VG.Proof.Pbkdf2.Stream.Arm (count_loop addr3 left_z left_val)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_add)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)

/-! ## Words of a constant, and words XORed with a constant -/

/-- `n` words of `r1` stored at `[r4 + o]`, `[r4 + o + 4]`, … -/
theorem fillW_ok {y : BitVec 32} {o : Nat} {b : Byte} (n : Nat) (ho : o + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = b ++ b ++ b ++ b →
    s.gpr .r4 = y → y.toNat + o + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (o + 4 * k)) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr y + BitVec.ofNat 64 o) (List.replicate (4 * n) b) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.str .r1 .r4 (o + 4 * k)) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hc hy fy hout k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih (by omega_arith) _ s Q hc hy (by omega_using [fy]) (fun j hj => hout j (by omega_arith)) fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (o + 4 * n)) (by omega_arith)
      (by rw [g₁, hy, addr_add (by omega_arith)]) (by rw [wr₁]; exact hout n (by omega_arith)) fun s₂ u₂ => ?_
    refine k s₂ (by rw [u₂.gpr, g₁]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁]) (by rw [u₂.sp, sp₁]) ?_
    rw [u₂.mem, m₁, g₁, hc, MdKeys.writeW_rep, ← Memory.add_ofNat,
      Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate]) (by simp; omega_arith),
      List.replicate_append_replicate, show 4 * n + 4 = 4 * (n + 1) by omega_arith]

/-- The outer state's buffer, from the inner one's: `n` words of
`[r4 + N + 4 k]`, XORed with `r1 = 0x6a6a6a6a`, into `[r5 + N + 4 k]`. -/
theorem opadW_ok (H : Hash) {x y : BitVec 32} (n : Nat) (ho : H.N + 4 * n ≤ 4096) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r1 = 0x6a6a6a6a → s.gpr .r4 = x →
    s.gpr .r5 = y → x.toNat + H.N + 4 * n ≤ 2 ^ 32 → y.toNat + H.N + 4 * n ≤ 2 ^ 32 →
    (∀ k < n, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    (∀ k < n, InRegions s.wr (State.addr y + BitVec.ofNat 64 (H.N + 4 * k)) 4) →
    Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N, 4 * n⟩ ⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ →
    (∀ s', (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr y + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q h1 hx hy fx fy hin hout hsep k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega_arith) _ s Q h1 hx hy (by omega_arith) (by omega_arith) (fun j hj => hin j (by omega_arith))
      (fun j hj => hout j (by omega_arith))
      ((hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
      fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) (by omega_arith)
      (by rw [g₁ _ (by decide), hx, addr_add (by omega_arith)]) (by rw [rd₁, wr₁]; exact hin n (by omega_arith))
      fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_str (a := State.addr y + BitVec.ofNat 64 (H.N + 4 * n)) (by omega_arith)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), hy, addr_add (by omega_arith)])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hout n (by omega_arith)) fun s₄ u₄ => ?_
    refine k s₄ (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, g₁ r hr])
      (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]) (by rw [u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    obtain hl : ((bytesAt s.mem (State.addr x + BitVec.ofNat 64 H.N) (4 * n)).map (· ^^^ (0x6a : Byte))).length =
        4 * n := by simp [bytesAt_length]
    obtain f₁ : Frame [⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩] s.mem s₁.mem := by
      rw [m₁]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
    obtain dX : ∀ r ∈ [(⟨State.addr y + BitVec.ofNat 64 H.N, 4 * n⟩ : Region)],
        Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 H.N + BitVec.ofNat 64 (4 * n), 4⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))
    obtain v : s₃.gpr .r12 = s₁.mem.readW (State.addr x + BitVec.ofNat 64 (H.N + 4 * n)) 32 ^^^ 0x6a6a6a6a := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h1]
    rw [u₄.mem, v, u₃.mem, u₂.mem, ← Memory.add_ofNat, ← Memory.add_ofNat,
      f₁.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) dX (by decide), MdKeys.c6a, MdKeys.writeW_xorRep, m₁,
      Memory.writeBytes_append' _ _ _ (by rw [hl]) (by simp [bytesAt_length]; omega_arith), ← List.map_append,
      ← bytesAt_add, show 4 * n + 4 = 4 * (n + 1) by omega_arith]

/-! ## The key loop -/

/-- After `j` bytes of the key loop, from `s`: the key at `kp`, its bytes,
XORed with `ipad`, written at `p + N`. -/
structure KeyInv (s : State) (kp p : BitVec 32) (N kl j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r, r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r
  r6 : t.gpr .r6 = kp + BitVec.ofNat 32 j
  r8 : t.gpr .r8 = p + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = BitVec.ofNat 32 (kl - j)
  mem : t.mem = writeBytes s.mem (State.addr p + BitVec.ofNat 64 N)
    ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))

theorem key_step (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩) {j : Nat} (hj : j < kl)
    {t : State} (h : KeyInv s kp p H.N kl j t) :
    WP isa (.block [.ldrb .r12 .r6 0, .dp .eor .r12 .r12 (.imm 0x36), .strb .r12 .r8 H.N,
      .dp .add .r6 .r6 (.imm 1), .dp .add .r8 .r8 (.imm 1), .subs .r7 .r7 (.imm 1)]) t
      fun t' => KeyInv s kp p H.N kl (j + 1) t' ∧ t'.z = decide (kl - (j + 1) = 0) := by
  obtain hl : ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad)).length = j := by
    simp [bytesAt_length]
  obtain hbyte : t.mem (State.addr kp + BitVec.ofNat 64 j) = s.mem (State.addr kp + BitVec.ofNat 64 j) := by
    rw [h.mem]
    refine (writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)).bytes
      (R := ⟨State.addr kp, kl⟩) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact hsep.sub_right (Region.sub_prefix (by omega_arith))) (by show kl ≤ 2 ^ 64; omega_arith) hj
  refine wp_ldrb (a := State.addr kp + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, addr3 (by omega_using [hj, hkp]), BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin j hj)
    fun t₁ u₁ => wp_eor (op2_imm (by decide)) fun t₂ u₂ => ?_
  refine wp_strb (a := State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) hN
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r8, addr3 (by omega_using [hj, hp])])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout j hj) fun t₃ u₃ => ?_
  refine wp_add (op2_imm (by decide)) fun t₄ u₄ => wp_add (op2_imm (by decide)) fun t₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun t₆ u₆ z₆ => WP.block_nil ?_
  obtain r7₅ : t₅.gpr .r7 = BitVec.ofNat 32 (kl - j) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r7]
  obtain v : (t₂.gpr .r12).setWidth 8 = s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad := by
    rw [u₂.gpr, u₁.gpr, MdKeys.xor_byte, hbyte]; rfl
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp],
    fun r h6 h7 h8 h12 => by
      rw [u₆.other r h7, u₅.other r h8, u₄.other r h6, u₃.gpr, u₂.other r h12, u₁.other r h12,
        h.other r h6 h7 h8 h12],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r6, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, BitVec.add_assoc, Proof.Pbkdf2.Stream.Arm.ofNat_succ32],
    by rw [u₆.gpr, r7₅, left_val hj], ?_⟩, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, v, u₂.mem, u₁.mem, h.mem]
    obtain e := VG.Proof.Hmac.Generic.Common.writeBytes_snoc s.mem (State.addr p + BitVec.ofNat 64 H.N)
      ((bytesAt s.mem (State.addr kp) j).map (· ^^^ Spec.Hmac.ipad))
      (s.mem (State.addr kp + BitVec.ofNat 64 j) ^^^ Spec.Hmac.ipad) (by rw [hl]; omega_using [hj, hkp])
    rw [hl] at e
    rw [e, VG.Proof.Hmac.Generic.Common.bytesAt_snoc', List.map_append, List.map_singleton]
  · rw [z₆, r7₅, left_z hj hkl]

/-- The key loop, skipped for an empty key: from the flags of `kl = 0`. -/
theorem key_ok (H : Hash) {s : State} {kp p : BitVec 32} {kl : Nat} (hkp : kp.toNat + kl ≤ 2 ^ 32)
    (hp : p.toNat + H.N + kl ≤ 2 ^ 32) (hkl : kl < 2 ^ 32) (hN : H.N < 4096)
    (hin : ∀ j < kl, InRegions (s.rd ++ s.wr) (State.addr kp + BitVec.ofNat 64 j) 1)
    (hout : ∀ j < kl, InRegions s.wr (State.addr p + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1)
    (hsep : Region.Disjoint ⟨State.addr kp, kl⟩ ⟨State.addr p + BitVec.ofNat 64 H.N, kl⟩)
    (h0 : KeyInv s kp p H.N kl 0 s) (hz : s.z = decide (kl = 0)) :
    WP isa (.ite .eq (.block []) H.keyLoop) s (KeyInv s kp p H.N kl kl) := by
  refine WP.ite (decide (kl = 0)) (by show eval .eq s = _; rw [eval_eq, hz]) (fun e => WP.block_nil ?_)
    fun e => ?_
  · have : kl = 0 := by simpa using e
    subst this; exact h0
  · exact count_loop (by simp at e; omega_arith) _ (fun j hj t h => key_step H hkp hp hkl hN hin hout hsep hj h) h0

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.Arm (initG below SavedRegs saveR savedRegs preserved_saved After below_eq covers_one
  init_call save_ok restore_ok)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_cmp wp_ldrSp op2_imm op2_reg cmp0)
open VG.Proof.Hmac.Common (bytesAt_length xorPad_length)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open VG.Spec.Sha256 (bytesAt)
open VG.Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev keyR : Region := ⟨State.addr (kp s₀), kl s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

section
variable (H : Hash) (sc : Nat) (s₀ : State)

abbrev inR : Region := ⟨State.addr (inn s₀), H.N + H.B⟩
abbrev outR : Region := ⟨State.addr (out s₀), H.N + H.B⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
/-- The compression function's scratch space. -/
abbrev cmpR : Region := ⟨State.addr (scr s₀), H.so⟩

end

structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_s : (outR H s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR H s₀)
  a_o : (argR s₀).Disjoint (outR H s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_i : (below s₀).Disjoint (inR H s₀)
  b_o : (below s₀).Disjoint (outR H s₀)
  b_k : (below s₀).Disjoint (keyR s₀)
  b_s : (below s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  no : (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.st.buf ≤ 8 * sc

theorem pre_of {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀)
    (hfit : H.st.buf ≤ 8 * sc) : Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS : hH.SH.stateBytes = H.N + H.B := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, hfit⟩

/-! ## Sizes and regions -/

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hz hp

theorem bounds : H.st.buf = 8 * H.st.W + 36 ∧ 8 * H.st.W + 36 ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 32 ∧
    H.so ≤ 8 * H.st.W ∧ H.st.W ≤ 64 ∧ H.N ≤ 64 ∧ H.N % 4 = 0 ∧ H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 ∧
    (inn s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧ (out s₀).toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
    (kp s₀).toNat + kl s₀ ≤ 2 ^ 32 ∧ kl s₀ ≤ H.B := by
  obtain hB : H.B % 4 = 0 ∧ 64 ≤ H.B ∧ H.B ≤ 128 := by rcases hz.B with h | h <;> rw [h] <;> decide
  exact ⟨rfl, hp.fits, hp.nw, hz.so, hz.W, hz.N64, hz.N4, hB.1, hB.2.1, hB.2.2, hp.ni, hp.no, hp.nk, hp.kl_le⟩

theorem save_sub : Region.Sub (saveR H.st (scr s₀)) (scR sc s₀) := by
  have := bounds hz hp; exact Offset.sub_base _ (by omega_arith)

theorem cmp_sub : Region.Sub (cmpR H s₀) (scR sc s₀) := by
  have := bounds hz hp; exact Region.sub_prefix (by omega_arith)

theorem save_cmp : (saveR H.st (scr s₀)).Disjoint (cmpR H s₀) := by
  have := bounds hz hp
  exact Offset.disjoint_base _ (by omega_arith) (hz.buf_le64)

omit hz hp in
/-- A part of a state at `p`. -/
theorem st_sub (p : BitVec 32) {a n : Nat} (h : a + n ≤ H.N + H.B) :
    Region.Sub ⟨State.addr p + BitVec.ofNat 64 a, n⟩ ⟨State.addr p, H.N + H.B⟩ := Offset.sub_base _ h

/-- The states, `scratch` and the stack below the stack pointer, as the code sees them. -/
theorem st_facts {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨State.addr p, H.N + H.B⟩ (scR sc s₀) ∧ (below s₀).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧
      (saveR H.st (scr s₀)).Disjoint ⟨State.addr p, H.N + H.B⟩ ∧ p.toNat + (H.N + H.B) ≤ 2 ^ 32 ∧
      ⟨State.addr p, H.N + H.B⟩ ∈ s₀.wr := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hz hp), hp.ni, by rw [hp.wr]; simp⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hz hp), hp.no, by rw [hp.wr]; simp⟩

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below the stack pointer. -/
abbrev wrs (H : Hash) (sc : Nat) (s₀ : State) : List Region := [inR H s₀, outR H s₀, scR sc s₀, below s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (H : Hash) (sc : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = out s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H.st (scr s₀) s₀ s.mem
  frame : Frame (wrs H sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

section
variable {H : Hash} {sc : Nat} {s₀ : State}

theorem KR.keep {s s' : State} (h : KR H sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H.st (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs H sc s₀, Region.Sub r r') : KR H sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r11, h.saved.frame H.st hf hs,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s s' : State} (h : KR H sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR H sc s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

/-- The key, while `KR` holds. -/
theorem KR.key {s : State} (hp : Pre H sc s₀) (hk : KR H sc s₀ s) :
    bytesAt s.mem (State.addr (kp s₀)) (kl s₀) = bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀) :=
  Memory.frame_bytesAt hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.k_i
    · exact hp.k_o
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (s₀.gpr .r3).isLt (by decide)))

end

/-! ## The pieces -/

/-- The offsets of the buffers in a state can be added as immediates. -/
theorem enc_small : ∀ n < 65, encodable (BitVec.ofNat 32 n) = true := by decide

section
variable {H : Hash} (hz : Sizes H) {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hz hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ fun s => KR H sc s₀ s ∧ s.gpr .r6 = kp s₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (kl s₀) := by
  obtain ⟨hb, hf, nw, -, hW, -⟩ := bounds hz hp
  obtain hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  unfold Hash.initPrologue
  simp only [List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (by rw [hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok H.st (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (L := 8 * sc) (by omega_arith) nw
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  obtain e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain hm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain f₂' : Frame [saveR H.st (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H.st fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    hm ▸ f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR sc s₀, by simp, save_sub hz hp⟩⟩,
    by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- A call of the streaming `init` on the state at `p`, in `r0`. -/
theorem initCall_ok (hH : HashOK H) {t : State} (hk : KR H sc s₀ t) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (h0 : t.gpr .r0 = p) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = t.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (.call H.st.initN H.st.initC) t Q := by
  obtain ⟨_, _, dV, np, hin⟩ := st_facts hz hp hpR
  have hS : H.st.S = H.N + H.B := hz.S
  refine init_call hH.stream (st := p) h0 (by rw [hS]; exact np) (by rw [hk.wr, hS]; exact covers_one hin)
    fun s' ha hr => ?_
  rw [hS] at ha
  have f := ha.frame
  rw [below_eq hk.sp] at f
  have f' : Frame [⟨State.addr p, H.N + H.B⟩, below s₀] t.mem s'.mem := f
  refine hQ s' (hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f' ?_ ?_)
    (fun r hr => ?_) f' hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV
    · exact hp.b_s.symm.sub_left (save_sub hz hp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR H s₀, by simp, fun _ h => h⟩
      · exact ⟨outR H s₀, by simp, fun _ h => h⟩
    · exact ⟨below s₀, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.cs .r6 (by decide) (by decide)
    · exact ha.cs .r7 (by decide) (by decide)

omit hz hp in
/-- `r0` at the state in `st`. -/
theorem initArg_ok {s : State} (hk : KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) :
    WP isa (.block [.mov .r0 (.reg st)]) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = p ∧
      (∀ r ∈ [Reg.r6, .r7], t.gpr r = s.gpr r) ∧ t.mem = s.mem :=
  wp_mov (op2_reg _ _) fun _ u₁ => WP.block_nil ⟨hk.upd (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide) u₁,
    by rw [u₁.gpr]; rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hk.r4, hk.r5],
    fun r hr => u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                               rcases hr with rfl | rfl <;> decide), u₁.mem⟩

/-- A call of the streaming `init` on the state at `p`, in `st`. -/
theorem callInit_ok (hH : HashOK H) {s : State} (hk : KR H sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → (∀ r ∈ [Reg.r6, .r7], s'.gpr r = s.gpr r) →
      Frame [⟨State.addr p, H.N + H.B⟩, below s₀] s.mem s'.mem → hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (H.st.callInit st) s Q := by
  obtain hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  unfold Impl.Pbkdf2.Stream.Arm.Hash.callInit
  exact WP.seq (WP.mono (initArg_ok hk hst) fun t ⟨k, d, g, m⟩ =>
    initCall_ok hz hp hH k hpR d fun s' k' g' f r => hQ s' k' (fun r hr => (g' r hr).trans (g r hr)) (m ▸ f) r)

/-- A word of the buffer of the state at `p`. -/
theorem buf_word {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) {k : Nat} (hk : k < H.B / 4) :
    InRegions s₀.wr (State.addr p + BitVec.ofNat 64 (H.N + 4 * k)) 4 := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, -⟩ := bounds hz hp
  obtain ⟨-, -, -, np, hin⟩ := st_facts hz hp hpR
  exact ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

/-- `ipad` in every byte of the inner buffer, and the flags of `key_len = 0`. -/
theorem fill_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀)) :
    WP isa (.block H.fillIpad) s fun t => KR H sc s₀ t ∧ t.gpr .r6 = kp s₀ ∧
      t.gpr .r7 = BitVec.ofNat 32 (kl s₀) ∧ t.gpr .r8 = inn s₀ ∧ t.z = decide (kl s₀ = 0) ∧
      t.mem = writeBytes s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) (List.replicate H.B 0x36) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, -⟩ := bounds hz hp
  obtain h4 : 4 * (H.B / 4) = H.B := by omega_arith
  simp only [Hash.fillIpad, List.cons_append, List.append_assoc]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  obtain c₂ : s₂.gpr .r1 = (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) ++ (0x36 : Byte) := by
    rw [u₂.gpr, u₁.gpr]; decide
  obtain hr4 : s₂.gpr .r4 = inn s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4]
  refine fillW_ok (H.B / 4) (by omega_arith) _ s₂ _ c₂ hr4 (by omega_arith)
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact buf_word hz hp (.inl rfl) hj) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r1 → r ≠ .r8 → s₅.gpr r = s.gpr r := fun r h1 h8 => by
    rw [f₅.gpr, u₄.other r h8, g₃, u₂.other r h1, u₁.other r h1]
  obtain sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain f : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₅.mem := by
    rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
    exact writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [f₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [f₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [f₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp]) (fun r hr => g r (by revert hr; decide +revert)
        (by revert hr; decide +revert)) f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩),
    by rw [g _ (by decide) (by decide), h6], by rw [g _ (by decide) (by decide), h7],
    by rw [f₅.gpr, u₄.gpr, g₃, hr4], ?_, by rw [f₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]⟩
  rw [z₅, u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide), h7,
    cmp0 (s₀.gpr .r3).isLt]

/-- The key loop: the key XORed with `ipad` over the start of the inner buffer. -/
theorem keys_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀) (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀))
    (h8 : s.gpr .r8 = inn s₀) (hzf : s.z = decide (kl s₀ = 0))
    (hm : bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36) :
    WP isa (.ite .eq (.block []) H.keyLoop) s fun t => KR H sc s₀ t ∧
      Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B =
        (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)).map (· ^^^ ipad) ++ List.replicate (H.B - kl s₀) ipad := by
  obtain ⟨-, -, -, -, -, hN, -, -, hB64, hB, ni, -, nk, hkl⟩ := bounds hz hp
  obtain kl32 : kl s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  obtain hin : ∀ j < kl s₀, InRegions (s.rd ++ s.wr) (State.addr (kp s₀) + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hk.rd, hp.rd]; exact ⟨keyR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_using [hj, nk])⟩
  obtain hout : ∀ j < kl s₀, InRegions s.wr (State.addr (inn s₀) + BitVec.ofNat 64 H.N + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hk.wr, hp.wr, Memory.add_ofNat]
      exact ⟨inR H s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hsep : Region.Disjoint ⟨State.addr (kp s₀), kl s₀⟩ ⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, kl s₀⟩ :=
    hp.k_i.sub_right (st_sub _ (by omega_arith))
  obtain h0 : KeyInv s (kp s₀) (inn s₀) H.N (kl s₀) 0 s :=
    ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, by rw [h6]; exact (BitVec.add_zero _).symm,
      by rw [h8]; exact (BitVec.add_zero _).symm, by rw [h7, Nat.sub_zero],
      by rw [show bytesAt s.mem (State.addr (kp s₀)) 0 = [] from rfl, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (key_ok H (by omega_arith) (by omega_arith) kl32 (by omega_arith) hin hout hsep h0 hzf) fun t ht => ?_
  obtain hl : ((bytesAt s.mem (State.addr (kp s₀)) (kl s₀)).map (· ^^^ ipad)).length = kl s₀ := by
    simp [bytesAt_length]
  obtain sB := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain ft : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Memory.contains_base hkl)
  refine ⟨hk.keep ht.rd ht.wr ht.sp (fun r hr => ht.other r (by revert hr; decide +revert)
      (by revert hr; decide +revert) (by revert hr; decide +revert) (by revert hr; decide +revert)) ft
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.symm.sub_left (save_sub hz hp)).sub_right sB)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sB⟩), ft, ?_⟩
  rw [ht.mem, MdKeys.bytes_over (by rw [hl]; omega_arith) (hz.B_lt64) hm, hl, hk.key hp]
  rfl

/-- What the compression of the buffer of the state at `p` needs. -/
theorem callOk {s : State} (hk : KR H sc s₀ s) {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀)
    (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = scr s₀) (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) :
    CallOk s H.N H.B H.so p (scr s₀) (p + BitVec.ofNat 32 H.N) := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := bounds hz hp
  obtain ⟨dS, _, _, np, hin⟩ := st_facts hz hp hpR
  obtain ap : State.addr (p + BitVec.ofNat 32 H.N) = State.addr p + BitVec.ofNat 64 H.N := addr_add (by omega_using [np, hB64])
  obtain tp : (p + BitVec.ofNat 32 H.N).toNat = p.toNat + H.N := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := H.N) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  obtain sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (Nat.le_add_right _ _)
  obtain sB := st_sub (H := H) p (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain sS : scR sc s₀ ∈ s.wr := by rw [hk.wr, hp.wr]; simp
  obtain hin' : ⟨State.addr p, H.N + H.B⟩ ∈ s.wr := by rw [hk.wr]; exact hin
  refine ⟨h0, h3, h6, by omega_using [np], by rw [tp]; omega_using [np], by omega_arith, dS.sub_left sN |>.sub_right (cmp_sub hz hp),
    by rw [ap]; exact Offset.disjoint_base _ (Nat.le_refl _) (hz.NB_le64),
    by rw [ap]; exact dS.sub_left sB |>.sub_right (cmp_sub hz hp), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ap]; exact ⟨_, List.mem_append_right _ hin', H.N, rfl, by simp only; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ hin', 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ sS, 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hin', 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩
    · exact ⟨_, sS, 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩

/-- The outer buffer from the inner one, and the inner state's compression set up. -/
theorem opad_ok {s : State} (hk : KR H sc s₀ s) :
    WP isa (.block H.fillOpad) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = inn s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N ∧
      t.mem = writeBytes s.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N)
        ((bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a)) := by
  obtain ⟨-, -, -, -, -, hN, -, hB4, hB64, hB, ni, no, -⟩ := bounds hz hp
  obtain h4 : 4 * (H.B / 4) = H.B := by omega_arith
  obtain sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  simp only [Hash.fillOpad, List.cons_append, List.append_assoc]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
  obtain c₂ : s₂.gpr .r1 = 0x6a6a6a6a := by rw [u₂.gpr, u₁.gpr]; decide
  refine opadW_ok H (H.B / 4) (by omega_arith) _ s₂ _ c₂ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r4])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hk.r5]) (by omega_arith) (by omega_arith)
    (fun j hj => by rw [u₂.wr, u₂.rd, u₁.wr, u₁.rd, hk.wr, hk.rd]
                    exact Hmac.Generic.Common.InRegions.right' (buf_word hz hp (.inl rfl) hj))
    (fun j hj => by rw [u₂.wr, u₁.wr, hk.wr]; exact buf_word hz hp (.inr rfl) hj)
    (by rw [h4]; exact (hp.i_o.sub_left sBI).sub_right sBO) fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  rw [h4, u₂.mem, u₁.mem] at m₃
  refine wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_add (op2_imm (enc_small _ (by omega_arith))) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h12 => by
    rw [g₃ r h12, u₂.other r h1, u₁.other r h1]
  obtain hl : ((bytesAt s.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  obtain f : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s.mem s₆.mem := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃]; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  refine ⟨hk.keep (by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr])
      (by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp])
      (fun r hr => by
        rw [u₆.other r (by revert hr; decide +revert), u₅.other r (by revert hr; decide +revert),
          u₄.other r (by revert hr; decide +revert), g r (by revert hr; decide +revert) (by revert hr; decide +revert)])
      f
      (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.o_s.symm.sub_left (save_sub hz hp)).sub_right sBO)
      (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨_, by simp, sBO⟩),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g _ (by decide) (by decide), hk.r4],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g _ (by decide) (by decide), hk.r11],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g _ (by decide) (by decide), hk.r4],
    by rw [u₆.mem, u₅.mem, u₄.mem, m₃]⟩

/-- The two blocks, as the constant-time proof needs them. -/
theorem blocks_ok {s : State} (hk : KR H sc s₀ s) (h6 : s.gpr .r6 = kp s₀)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 (kl s₀)) :
    WP isa H.blocks s fun t => KR H sc s₀ t ∧ t.gpr .r0 = inn s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N := by
  have := (bounds hz hp).2.2.2.2.2.2.2.2.2.1
  refine WP.seq (WP.mono (fill_ok hz hp hk h6 h7) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ d₄ c₄ e₄ z₄ (by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (hz.B_lt64)])) fun s₅ ⟨k₅, _⟩ => ?_)
  exact WP.mono (opad_ok hz hp k₅) fun _ ⟨k₆, a, b, c, _⟩ => ⟨k₆, a, b, c⟩

/-- The compression of the buffer of the state at `p`, at `r0`, with its
buffer at `r6` and `scratch` at `r3`. -/
theorem cmpS_ok (hH : HashOK H) {s : State} (hk : KR H sc s₀ s) {p : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (h0 : s.gpr .r0 = p) (h3 : s.gpr .r3 = scr s₀)
    (h6 : s.gpr .r6 = p + BitVec.ofNat 32 H.N) {Q : State → Prop}
    (hQ : ∀ s', KR H sc s₀ s' → s'.gpr .r3 = scr s₀ →
      Frame [⟨State.addr p, H.N⟩, cmpR H s₀] s.mem s'.mem →
      hH.md.stateAt s'.mem (State.addr p) = hH.md.compress (hH.md.stateAt s.mem (State.addr p))
        (hH.md.blockAt s.mem (State.addr p + BitVec.ofNat 64 H.N)) → Q s') :
    WP isa H.compressBlock s Q := by
  obtain ⟨hb, hf, nw, hso, hW, hN, -, -, hB64, hB, -⟩ := bounds hz hp
  obtain ⟨_, _, dV, np, _⟩ := st_facts hz hp hpR
  obtain sN : Region.Sub ⟨State.addr p, H.N⟩ ⟨State.addr p, H.N + H.B⟩ := Region.sub_prefix (Nat.le_add_right _ _)
  refine compressBlock_ok hH.comp (callOk hz hp hk hpR h0 h3 h6) fun s' hrd hwr hcs h0' h3' hsp hfr hst => ?_
  rw [addr_add (by omega_arith)] at hst
  refine hQ s' (hk.keep hrd hwr hsp (fun r hr => hcs r (kregs_pres r hr).1 (kregs_pres r hr).2) hfr ?_ ?_) h3' hfr hst
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV.sub_right sN
    · exact save_cmp hz hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rcases hpR with rfl | rfl
      · exact ⟨inR H s₀, by simp, sN⟩
      · exact ⟨outR H s₀, by simp, sN⟩
    · exact ⟨scR sc s₀, by simp, cmp_sub hz hp⟩

omit hp in
/-- The outer state's compression set up. -/
theorem toOuter_ok {s : State} (hk : KR H sc s₀ s) (h3 : s.gpr .r3 = scr s₀) :
    WP isa (.block H.toOuter) s fun t => KR H sc s₀ t ∧ t.gpr .r0 = out s₀ ∧ t.gpr .r3 = scr s₀ ∧
      t.gpr .r6 = out s₀ + BitVec.ofNat 32 H.N ∧ t.mem = s.mem := by
  have hz_N64 := hz.N64
  unfold Hash.toOuter
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (enc_small _ (by omega_arith))) fun s₂ u₂ => WP.block_nil ?_
  exact ⟨(hk.upd (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr, hk.r5],
    by rw [u₂.other _ (by decide), u₁.other _ (by decide), h3], by rw [u₂.gpr, u₁.other _ (by decide), hk.r5],
    by rw [u₂.mem, u₁.mem]⟩

end

/-! ## Correctness -/

section
variable {H : Hash} {sc : Nat} {s₀ : State} (hH : HashOK H) (hp : Pre H sc s₀)
include hH hp

omit hp in
theorem keep_st {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N⟩ r) : hH.md.stateAt m' p = hH.md.stateAt m p :=
  hH.md.stateAt_congr fun i hi => hf.bytes (R := ⟨p, H.N⟩) hd (by have := hH.sizes.N64; show H.N ≤ 2 ^ 64; omega_arith) hi

omit hp in
theorem keep_repr {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.N + H.B⟩ r) {x : List Byte} (hr : hH.md.Repr hH.iv m p x) :
    hH.md.Repr hH.iv m' p x :=
  hH.md.repr_congr (by have hH_B_ge := hH.B_ge; omega_arith) (fun i hi => hf.bytes (R := ⟨p, H.N + H.B⟩) hd
    (by have hH_B_le := hH.B_le; have := hH.sizes.N64; show H.N + H.B ≤ 2 ^ 64; omega_arith) hi) hr

theorem correct :
    WP isa H.hmacInit s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  have hz := hH.sizes
  obtain ⟨hb, hf, nw, hso, hW, hN, hN4, hB4, hB64, hB, ni, no, nk, hkl⟩ := bounds hz hp
  have hl := hH.link
  -- Where things are.
  obtain sNI := st_sub (H := H) (inn s₀) (a := 0) (n := H.N) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)
  obtain sNO := st_sub (H := H) (out s₀) (a := 0) (n := H.N) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _)
  rw [BitVec.add_zero] at sNI sNO
  obtain sBI := st_sub (H := H) (inn s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain sBO := st_sub (H := H) (out s₀) (a := H.N) (n := H.B) (Nat.le_refl _)
  obtain nb : ∀ (x : BitVec 32), Region.Disjoint ⟨State.addr x, H.N⟩ ⟨State.addr x + BitVec.ofNat 64 H.N, H.B⟩ :=
    fun _ => Offset.base_disjoint _ (Nat.le_refl _) (hz.NB_le64)
  obtain iv0 : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := (hl.repr _ _ _ h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  refine WP.seq (WP.mono (pro_ok hz hp) fun s₁ ⟨k₁, r6₁, r7₁⟩ => ?_)
  refine WP.seq (callInit_ok hz hp hH k₁ (.inl ⟨rfl, rfl⟩) fun s₂ k₂ g₂ _ r₂ => ?_)
  refine WP.seq (callInit_ok hz hp hH k₂ (.inr ⟨rfl, rfl⟩) fun s₃ k₃ g₃ f₃ r₃ => ?_)
  obtain r6₃ : s₃.gpr .r6 = kp s₀ := by rw [g₃ _ (by simp), g₂ _ (by simp), r6₁]
  obtain r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 (kl s₀) := by rw [g₃ _ (by simp), g₂ _ (by simp), r7₁]
  obtain vI₃ : hH.md.stateAt s₃.mem (State.addr (inn s₀)) = hH.iv := by
    rw [keep_st hH f₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.i_o.sub_left sNI
      · exact hp.b_i.symm.sub_left sNI), iv0 r₂]
  obtain vO₃ := iv0 r₃
  refine WP.seq (WP.seq (WP.mono (fill_ok hz hp k₃ r6₃ r7₃) fun s₄ ⟨k₄, d₄, c₄, e₄, z₄, m₄⟩ => ?_))
  obtain rep₄ : bytesAt s₄.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B = List.replicate H.B 0x36 := by
    rw [m₄, bytesAt_writeBytes_self' (List.length_replicate ..) (hz.B_lt64)]
  obtain f₄ : Frame [⟨State.addr (inn s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [List.length_replicate]; exact Region.contains_self _ _)
  refine WP.seq (WP.mono (keys_ok hz hp k₄ d₄ c₄ e₄ z₄ rep₄) fun s₅ ⟨k₅, f₅, bI₅⟩ => ?_)
  refine WP.mono (opad_ok hz hp k₅) fun s₆ ⟨k₆, a₆, b₆, c₆, m₆⟩ => ?_
  obtain hl6 : ((bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ (0x6a : Byte))).length =
      H.B := by simp [bytesAt_length]
  obtain f₆ : Frame [⟨State.addr (out s₀) + BitVec.ofNat 64 H.N, H.B⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hl6]; exact Region.contains_self _ _)
  obtain bO₆ : bytesAt s₆.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N) H.B =
      (bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B).map (· ^^^ 0x6a) := by
    rw [m₆, bytesAt_writeBytes_self' hl6 (hz.B_lt64)]
  obtain bI₆ : bytesAt s₆.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B =
      bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B :=
    Memory.frame_bytesAt f₆ (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sBI).sub_right sBO) (by omega_using [hB])
  -- The hash values are those `init` left.
  obtain vI₆ : hH.md.stateAt s₆.mem (State.addr (inn s₀)) = hH.iv := by
    rw [keep_st hH f₆ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.sub_left sNI).sub_right sBO),
      keep_st hH f₅ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hH f₄ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _), vI₃]
  obtain vO₆ : hH.md.stateAt s₆.mem (State.addr (out s₀)) = hH.iv := by
    rw [keep_st hH f₆ (by simp only [List.mem_singleton]; rintro r rfl; exact nb _),
      keep_st hH f₅ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI),
      keep_st hH f₄ (by
        simp only [List.mem_singleton]; rintro r rfl; exact (hp.i_o.symm.sub_left sNO).sub_right sBI), vO₃]
  refine WP.seq (cmpS_ok hz hp hH k₆ (.inl rfl) a₆ b₆ c₆ fun s₇ k₇ r3₇ f₇ e₇ => ?_)
  refine WP.seq (WP.mono (toOuter_ok hz k₇ r3₇) fun s₈ ⟨k₈, a₈, b₈, c₈, m₈⟩ => ?_)
  refine WP.seq (cmpS_ok hz hp hH k₈ (.inr rfl) a₈ b₈ c₈ fun s₉ k₉ _ f₉ e₉ => ?_)
  -- The key.
  obtain hK : xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ipad =
      bytesAt s₅.mem (State.addr (inn s₀) + BitVec.ofNat 64 H.N) H.B := by
    rw [bI₅, MdKeys.blockKey_short _ (by rw [bytesAt_length, hH.hB]; exact hkl), MdKeys.xorPad_short,
      bytesAt_length, hH.hB]
  obtain hKl : (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ipad).length = H.B := by
    rw [hK, bytesAt_length]
  -- The inner state.
  obtain rI₇ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega_using [hB64]) hKl (by rw [bI₆, hK]) (by rw [e₇, vI₆])
  obtain dI₉ : ∀ r ∈ [(⟨State.addr (out s₀), H.N⟩ : Region), cmpR H s₀],
      Region.Disjoint ⟨State.addr (inn s₀), H.N + H.B⟩ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o.sub_right sNO
    · exact hp.i_s.sub_right (cmp_sub hz hp)
  obtain rI₉ := keep_repr hH f₉ dI₉ (m₈ ▸ rI₇)
  -- The outer state.
  obtain d₇ : ∀ {a n : Nat}, a + n ≤ H.N + H.B → ∀ r ∈ [(⟨State.addr (inn s₀), H.N⟩ : Region), cmpR H s₀],
      Region.Disjoint ⟨State.addr (out s₀) + BitVec.ofNat 64 a, n⟩ r := by
    intro a n h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (hp.i_o.symm.sub_left (st_sub _ h)).sub_right sNI
    · exact (hp.o_s.sub_left (st_sub _ h)).sub_right (cmp_sub hz hp)
  obtain vO₈ : hH.md.stateAt s₈.mem (State.addr (out s₀)) = hH.iv := by
    rw [m₈, keep_st hH f₇ (by have := d₇ (a := 0) (n := H.N) (by rw [Nat.zero_add]; exact Nat.le_add_right _ _); rwa [BitVec.add_zero] at this), vO₆]
  obtain bO₈ : bytesAt s₈.mem (State.addr (out s₀) + BitVec.ofNat 64 H.N) H.B =
      xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) opad := by
    rw [m₈, Memory.frame_bytesAt f₇ (d₇ (Nat.le_refl _)) (by omega_using [hB]), bO₆, ← hK, MdKeys.xorOpad_ipad]
  obtain rO₉ := Md.repr_block (H := hH.md) (iv := hH.iv) (by omega_arith)
    (by rw [xorPad_length, ← xorPad_length _ ipad, hKl]) bO₈ (by rw [e₉, vO₈])
  -- The end.
  obtain hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₉.wr := by rw [k₉.wr, hp.wr]; simp
  refine WP.mono (restore_ok H.st k₉.r11 hW k₉.saved hsc (by omega_arith) nw) fun s' ⟨hm, _, _, hsp, hg, _⟩ => ?_
  refine ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, k₉.sp]⟩, ?_⟩
  show hH.SH.Repr s'.mem (State.addr (inn s₀)) _ ∧ hH.SH.Repr s'.mem (State.addr (out s₀)) _
  rw [hm]
  exact ⟨hH.back _ _ _ rI₉, hH.back _ _ _ rO₉⟩

end

end VG.Proof.Pbkdf2.Md.Arm.HmacInit

end

end


/-!
# HMAC's `init` over a Merkle–Damgård hash function on ARMv7: constant time

As `finalize` (`HmacFinCT.lean`): correctness determines our registers from
the public arguments alone, so the taint analysis proves the blocks between
the calls constant time from them (`Checks`, evaluated for each hash
function); the calls of the streaming `init` are constant time by its own
proof (`init_rel`, `Proof/Pbkdf2/Stream/Arm/Hash.lean`), and those of the
compression function by its own (`compressBlock_rel`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm.HmacInit

open VG VG.Arm
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (initG init_rel covers_one)

/-- The registers that the pieces between the calls use, which hold our
variables: `inner`, `outer`, the key and its length, and `scratch`. -/
abbrev regsK : List Reg := [.r4, .r5, .r6, .r7, .r11]

/-- The taint checks of the pieces of `init` between its calls, which
depend on the hash function's sizes. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block H.initPrologue) hc).isSome = true
  arg : ∀ st ∈ [Reg.r4, .r5], ∃ hc, (taint.check (Taint.ofRegs regsK) (.block [.mov .r0 (.reg st)]) hc).isSome = true
  blocks : ∃ hc, (taint.check (Taint.ofRegs regsK) H.blocks hc).isSome = true
  toOuter : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.toOuter) hc).isSome = true
  restore : ∃ hc, (taint.check (Taint.ofRegs kregs) (.block H.st.restore) hc).isSome = true

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

section
variable {H : Hash} {sc : Nat} {s₀ s₀' : State}

theorem kr_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KR H sc s₀ s) (h' : KR H sc s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, out, out, hq.r1]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

/-- `KR`, with the key and its length in `r6` and `r7`. -/
def KK (H : Hash) (sc : Nat) (s₀ s : State) : Prop :=
  KR H sc s₀ s ∧ s.gpr .r6 = kp s₀ ∧ s.gpr .r7 = BitVec.ofNat 32 (kl s₀)

theorem kk_agree (hq : PubEq s₀ s₀') {s s' : State} (h : KK H sc s₀ s) (h' : KK H sc s₀' s') :
    ∀ r ∈ regsK, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kr_agree hq h.1 h'.1 _ (by simp)
  · exact kr_agree hq h.1 h'.1 _ (by simp)
  · rw [h.2.1, h'.2.1, kp, kp, hq.r2]
  · rw [h.2.2, h'.2.2, kl, kl, hq.r3]
  · exact kr_agree hq h.1 h'.1 _ (by simp)

end

section
variable {H : Hash} (hH : HashOK H) {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀')
  (hq : PubEq s₀ s₀')
include hH hp hp' hq

/-- A call of the streaming `init` on the state in `st` (`r4` for `inner`,
`r5` for `outer`). -/
theorem callInit_rel (hc : Checks H) {st : Reg} {p : BitVec 32}
    (hst : st = .r4 ∧ p = inn s₀ ∨ st = .r5 ∧ p = out s₀) :
    RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') (H.st.callInit st)
      fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s' := by
  have hz := hH.sizes
  obtain hst' : st = .r4 ∧ p = inn s₀' ∨ st = .r5 ∧ p = out s₀' := by
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact .inl ⟨h1, by rw [h2, inn, inn, hq.r0]⟩
    · exact .inr ⟨h1, by rw [h2, out, out, hq.r1]⟩
  obtain hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain hpR' : p = inn s₀' ∨ p = out s₀' := by rcases hst' with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨_, _, _, np, hin⟩ := st_facts hz hp hpR
  obtain ⟨_, _, _, _, hin'⟩ := st_facts hz hp' hpR'
  have hS : H.st.S = H.N + H.B := hz.S
  let F : State → State → Prop := fun t₀ s => KR H sc t₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r6 = kp t₀ ∧
    s.gpr .r7 = BitVec.ofNat 32 (kl t₀)
  obtain ha : RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') (.block [.mov .r0 (.reg st)])
      fun s s' => F s₀ s ∧ F s₀' s' :=
    rel_agree (Taint.ofRegs regsK) (fun _ _ h h' => Taint.agree_ofRegs (kk_agree hq h h'))
      (hc.arg st (by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp))
      (fun _ ⟨k, r6, r7⟩ => WP.mono (initArg_ok k hst) fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
      (fun _ ⟨k, r6, r7⟩ => WP.mono (initArg_ok k hst') fun _ ⟨k', d, g, _⟩ =>
        ⟨k', d, by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
  unfold Impl.Pbkdf2.Stream.Arm.Hash.callInit
  refine ha.seq (rel_wp (init_rel hH.stream (st := p) fun s s' ⟨⟨k, d, _⟩, ⟨k', d', _⟩⟩ =>
      ⟨d, d', by rw [hS]; exact np, by rw [k.wr, hS]; exact covers_one hin, by rw [k'.wr, hS]; exact covers_one hin'⟩)
    (fun _ ⟨k, d, r6, r7⟩ => initCall_ok hz hp hH k hpR d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩)
    (fun _ ⟨k, d, r6, r7⟩ => initCall_ok hz hp' hH k hpR' d fun _ k' g _ _ =>
      ⟨k', by rw [g _ (by simp), r6], by rw [g _ (by simp), r7]⟩))

/-- The compression of the buffer of the state at `p`. -/
theorem cmpS_rel {p p' : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) (hpR' : p' = inn s₀' ∨ p' = out s₀')
    (he : p' = p) :
    RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = p ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = p + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = p' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = p' + BitVec.ofNat 32 H.N))
      H.compressBlock fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀') := by
  have hz := hH.sizes
  have e : scr s₀' = scr s₀ := hq.a0.symm
  exact rel_wp (compressBlock_rel (H := hH.md) (so := H.so) hH.comp (name := H.compN) (st := p) (scr := scr s₀)
      (src := p + BitVec.ofNat 32 H.N) fun s s' ⟨⟨k, a, b, c⟩, ⟨k', a', b', c'⟩⟩ => by
        obtain c₂ := callOk hz hp' k' hpR' a' b' c'
        rw [he, e] at c₂
        exact ⟨callOk hz hp k hpR a b c, c₂⟩)
    (fun _ ⟨k, a, b, c⟩ => cmpS_ok hz hp hH k hpR a b c fun _ k' r3 _ _ => ⟨k', r3⟩)
    (fun _ ⟨k, a, b, c⟩ => cmpS_ok hz hp' hH k hpR' a b c fun _ k' r3 _ _ => ⟨k', r3⟩)

include hH hp hp' hq in
theorem ct (hc : Checks H) : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have hz := hH.sizes
  obtain aw : ∀ {t : State}, Pre H sc t →
      t.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ t.wr, Region.Disjoint ⟨State.addr t.sp, 4⟩ r := fun {t} h => by
    obtain e : (⟨State.addr t.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr]
    refine ⟨h.spf, ?_⟩
    simp only [e, h.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_i
    · exact h.a_o
    · exact h.a_s
  obtain pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s' :=
    rel_agree (argTaint [.r0, .r1, .r2, .r3] 4) (fun s s' e e' => by
        rw [e, e']
        refine agree_argTaint (fun r hr => ?_) hq.sp (aw hp) (aw hp')
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by rw [show i = 0 by omega_using [hi]]; exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hz hp)
      (fun _ e => by rw [e]; exact pro_ok hz hp')
  obtain blk : RelCT isa (fun s s' => KK H sc s₀ s ∧ KK H sc s₀' s') H.blocks
      fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = inn s₀ ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = inn s₀ + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = inn s₀' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = inn s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs regsK) (fun _ _ h h' => Taint.agree_ofRegs (kk_agree hq h h')) hc.blocks
      (fun _ ⟨k, r6, r7⟩ => blocks_ok hz hp k r6 r7)
      (fun _ ⟨k, r6, r7⟩ => blocks_ok hz hp' k r6 r7)
  obtain tO : RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀'))
      (.block H.toOuter)
      fun s s' => (KR H sc s₀ s ∧ s.gpr .r0 = out s₀ ∧ s.gpr .r3 = scr s₀ ∧
          s.gpr .r6 = out s₀ + BitVec.ofNat 32 H.N) ∧
        (KR H sc s₀' s' ∧ s'.gpr .r0 = out s₀' ∧ s'.gpr .r3 = scr s₀' ∧ s'.gpr .r6 = out s₀' + BitVec.ofNat 32 H.N) :=
    rel_agree (Taint.ofRegs kregs) (fun _ _ h h' => Taint.agree_ofRegs (kr_agree hq h.1 h'.1)) hc.toOuter
      (fun _ ⟨k, r3⟩ => WP.mono (toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
      (fun _ ⟨k, r3⟩ => WP.mono (toOuter_ok hz k r3) fun _ ⟨k', a, b, c, _⟩ => ⟨k', a, b, c⟩)
  obtain ⟨_, hr⟩ := hc.restore
  obtain restore : RelCT isa (fun s s' => (KR H sc s₀ s ∧ s.gpr .r3 = scr s₀) ∧ (KR H sc s₀' s' ∧ s'.gpr .r3 = scr s₀'))
      (.block H.st.restore) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs) (fun _ _ h => Taint.agree_ofRegs (kr_agree hq h.1.1 h.2.1)) hr
  exact pro.seq ((callInit_rel hH hp hp' hq hc (.inl ⟨rfl, rfl⟩)).seq
    ((callInit_rel hH hp hp' hq hc (.inr ⟨rfl, rfl⟩)).seq
    (blk.seq ((cmpS_rel hH hp hp' hq (.inl rfl) (.inl rfl) hq.r0.symm).seq
    (tO.seq ((cmpS_rel hH hp hp' hq (.inr rfl) (.inr rfl) hq.r1.symm).seq restore))))))

end

/-! ## Verified -/

theorem pubEq_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State} (h : (initG S W).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- HMAC's `init` is verified against `initG`, for any hash function the
proof supports (`HashOK`), whose pieces of code the taint analysis accepts
(`Checks`). -/
theorem verified {H : Hash} (hH : HashOK H) (hc : Checks H) {sc : Nat} (hfit : H.st.buf ≤ 8 * sc)
    (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified Arm.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => correct hH (pre_of hH hs hfit), fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) (pubEq_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.Arm.HmacInit
