module

public import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

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
