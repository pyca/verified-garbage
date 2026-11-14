module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
public import VerifiedGarbage.Proof.Pbkdf2.MdKeys
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `init`

HMAC's `init` (`Impl/Pbkdf2/Md/X86_64.lean`) saves our caller's registers
(`pro_ok`), sets each state's hash value with the streaming `init`
(`callInit_ok`), writes `K₀ ⊕ ipad` into the inner state's buffer and
`K₀ ⊕ opad` into the outer one's (`keys_ok`: `ipad` sixteen bytes at a
time, `fill_ok`; the key XORed in, its whole 16-byte words, `key16_ok`, then
its other bytes, `key_ok`; then the outer buffer from the inner one sixteen
bytes at a time, `opad_ok`), compresses each buffer into its state's hash value, and loads our
caller's registers back. The compressions are `Hash.compBoth`, of which
`init` needs `BothOk`: the compression function on each buffer in turn
(`BothOk.twice`, from `cmp_ok`), or one call of a function that compresses
both at once (`BothOk.pair`, from `MdStream.X86_64.PairOk`), whichever the
hash function's code has (`HashOK.both`, `bothOk`). A state whose initial hash value has
absorbed the block in its buffer represents that block
(`Md.repr_block`). Constant time: the taint analysis checks the pieces
between the calls (`Checks`); the calls are constant time by the callees'
own proofs.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacInit

open VG.X86_64 VG.Proof.MdStream
open VG.Proof.MdStream.X86_64 (add_ofNat sx_ofNat zx_ofNat wp_mov wp_mov32i wp_addi wp_andi
  wp_store8 wp_movzx8 wp_cmp Upd CallOk compressAt_ok compressAt_rel ea_at ofInt_natCast
  ofNat_succ ofNat_pred ofNat_beq_zero sub_beq and_mask vbytes vbytes_length vbytes_getElem wp_movqx wp_xbin
  wp_movImm64' wp_movdquStoreX wp_shrX wp_testX WP.cons)
open VG.Impl.MdStream.X86_64 (compressAt at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash byteAt pairArgs)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG rel_taint rel_wp init_call init_rel SavedRegs saveR save_ok
  restore_ok count_loop ea_byteAt sx_one wp_xor32i xor_byte PubEq args repr_keep)
open VG.Proof.Hmac.Generic.Common (K0 K0_length covers_one InRegions.right' bytes_keep)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_getD' bytesAt_writeBytes_sep bytesAt_add extractLsb'_read)
open VG.Proof.Hmac.Generic.Common (bytesAt_writeBytes_self')
open VG.Proof.Pbkdf2.MdKeys (ipadBlk ipadBlk_length ipadBlk_zero ipadBlk_succ ipadBlk_eq writeBytes_set
  xorOpad_ipad)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## The precondition -/

section
variable (H : Hash) (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The compression function's working space. -/
abbrev calR : Region := ⟨scr s₀, H.P.so⟩
/-- Where our caller's registers are saved. -/
abbrev svR : Region := saveR H.stream (scr s₀)
/-- The buffer of the state at `p`. -/
abbrev bufOf (p : Addr) : Addr := p + BitVec.ofNat 64 H.P.N
/-- The key, padded to a block. -/
abbrev k0 : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.P.B

end

abbrev scR (sc : Nat) (s₀ : State) : Region := ⟨scr s₀, 8 * sc⟩

/-- The precondition, with the sizes of `H`. -/
structure Pre (H : Hash) (sc : Nat) (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.P.B
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR H s₀, outR H s₀, scR sc s₀]
  i_o : (inR H s₀).Disjoint (outR H s₀)
  i_s : (inR H s₀).Disjoint (scR sc s₀)
  o_s : (outR H s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR H s₀)
  k_o : (keyR s₀).Disjoint (outR H s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  ret_i : (retR s₀).Disjoint (inR H s₀)
  ret_o : (retR s₀).Disjoint (outR H s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR H s₀)
  stk_o : (stkR s₀).Disjoint (outR H s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.stream.buf ≤ 8 * sc

variable {H : Hash} (hH : HashOK H)

theorem pre_of {sc : Nat} {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.stream.buf ≤ 8 * sc) :
    Pre H sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The sizes the proof needs. -/
theorem sizes : H.P.N % 4 = 0 ∧ H.P.B % 4 = 0 ∧ H.P.N ≤ 64 ∧ 0 < H.P.B ∧ H.P.B ≤ 128 ∧
    H.P.so + 48 = 8 * H.stream.W ∧ H.stream.buf = 8 * H.stream.W + 48 ∧ H.stream.W ≤ 256 ∧
    8 * H.stream.W + 48 ≤ 8 * sc ∧ 8 * sc ≤ 2 ^ 64 := by
  have := hH.hN4; have := hH.N_le; have := hH.B_le; have := hH.B_pos; have := hH.hso; have := hp.nw
  have := hp.fits
  have hb : H.stream.buf = 8 * H.stream.W + 48 := rfl
  have hw : H.stream.W = (H.P.so + 48) / 8 := rfl
  have : H.P.B % 4 = 0 := by rcases hH.dims.B with h | h <;> omega_using [h]
  omega_arith

/-! ## The parts of the regions -/

theorem save_sub : Region.Sub (svR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sizes hH hp
  exact Offset.sub_base _ h

theorem cal_sub : Region.Sub (calR H s₀) (scR sc s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', -⟩ := sizes hH hp
  exact Region.sub_prefix (by omega_using [h, h'])

theorem cal_save : (calR H s₀).Disjoint (svR H s₀) := by
  obtain ⟨-, -, -, -, -, h, -, -, h', h''⟩ := sizes hH hp
  have := hp.nw
  exact Offset.base_disjoint _ (by omega_using [h]) (by omega_using [h', this])

omit hH hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega_using [])

/-- What a state's region is: writable, and apart from the others. -/
structure StOk (p : Addr) : Prop where
  mem : ⟨p, H.S⟩ ∈ s₀.wr
  sc : Region.Disjoint ⟨p, H.S⟩ (scR sc s₀)
  stk : (stkR s₀).Disjoint ⟨p, H.S⟩
  ret : (retR s₀).Disjoint ⟨p, H.S⟩
  key : (keyR s₀).Disjoint ⟨p, H.S⟩

omit hH in
theorem stOk_in : StOk (H := H) (sc := sc) (s₀ := s₀) (inn s₀) :=
  ⟨by rw [hp.wr]; simp, hp.i_s, hp.stk_i, hp.ret_i, hp.k_i⟩

omit hH in
theorem stOk_out : StOk (H := H) (sc := sc) (s₀ := s₀) (out s₀) :=
  ⟨by rw [hp.wr]; simp, hp.o_s, hp.stk_o, hp.ret_o, hp.k_o⟩

/-- A region the code may write while our caller's registers, the return
address and the key stay put. -/
structure Away (r : Region) : Prop where
  sv : (svR H s₀).Disjoint r
  ret : (retR s₀).Disjoint r
  key : (keyR s₀).Disjoint r

theorem away_st {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {r : Region}
    (h : Region.Sub r ⟨p, H.S⟩) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hs.sc.symm.sub_left (save_sub hH hp)).sub_right h, hs.ret.sub_right h, hs.key.sub_right h⟩

theorem away_cal : Away (H := H) (s₀ := s₀) (calR H s₀) :=
  ⟨(cal_save hH hp).symm, hp.ret_s.sub_right (cal_sub hH hp), hp.k_s.sub_right (cal_sub hH hp)⟩

theorem away_stk {r : Region} (h : Region.Sub r (stkR s₀)) : Away (H := H) (s₀ := s₀) r :=
  ⟨(hp.stk_s.symm.sub_left (save_sub hH hp)).sub_right h, stk_ret.symm.sub_right h, hp.stk_k.symm.sub_right h⟩

end

/-! ## What holds from the prologue on -/

/-- The registers and memory kept from the prologue on, with `rbx = b` (the
state being compressed). -/
structure KR (H : Hash) (s₀ : State) (b : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = b
  rbp : s.gpr .rbp = kp s₀
  r12 : s.gpr .r12 = out s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H.stream (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  key : ∀ i < kl s₀, s.mem (kp s₀ + BitVec.ofNat 64 i) = s₀.mem (kp s₀ + BitVec.ofNat 64 i)

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (ha : ∀ r ∈ rs, Away (H := H) (s₀ := s₀) r) : KR H s₀ b s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.rbp, (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13,
    (hg _ (by simp)).trans h.r15, h.saved.frame H.stream hf fun r hr => (ha r hr).sv,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (ha r hr).ret) (by decide)).trans h.ret,
    fun i hi => (hf.bytes (R := keyR s₀) (fun r hr => (ha r hr).key) (Nat.le_of_lt (s₀.gpr .rcx).isLt)
      hi).trans (h.key i hi)⟩

theorem KR.regs {s₀ s s' : State} {b : Addr} (h : KR H s₀ b s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR H s₀ b s' :=
  h.keep (rs := []) hrd hwr hg (by rw [hm]; exact Frame.refl _ _) (by simp)

/-! ## The prologue -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

theorem pro_ok : WP isa (.block H.initPrologue) s₀ (KR H s₀ (inn s₀)) := by
  obtain ⟨-, -, -, -, -, -, -, hW, hL, -⟩ := sizes hH hp
  unfold Hash.initPrologue
  refine save_ok H.stream (scr := scr s₀) rfl hW (by rw [hp.wr]; simp) hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13] → s₆.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2.2.2.2, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1, u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have hs : ∀ r ∈ [svR H s₀], (retR s₀).Disjoint r ∧ (keyR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl
    exact ⟨hp.ret_s.sub_right (save_sub hH hp), hp.k_s.sub_right (save_sub hH hp)⟩
  exact ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    g _ (by decide),
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁],
    hm ▸ sv₁,
    by rw [hm]; exact f₁.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => (hs r hr).1) (by decide),
    fun i hi => by
      rw [hm]; exact f₁.bytes (R := keyR s₀) (fun r hr => (hs r hr).2) (Nat.le_of_lt (s₀.gpr .rcx).isLt) hi⟩

end

/-! ## The calls of the streaming `init` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- A call of the streaming `init` on the state at `p`, from the register `st`. -/
theorem callInit_ok {b : Addr} {s : State} (hk : KR H s₀ b s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hst : StOk (H := H) (sc := sc) (s₀ := s₀) p) {Q : State → Prop}
    (hQ : ∀ s', KR H s₀ b s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.stream.callInit st) s Q := by
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => WP.block_nil ?_)
  have k₁ : KR H s₀ b s₁ := hk.regs u₁.rd u₁.wr (fun r hr => u₁.other r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.mem
  refine init_call hH.stream (st := p) (by rw [u₁.gpr, hs]) (by rw [k₁.wr]; exact covers_one hst.mem)
    (by rw [k₁.rsp]; exact hst.stk) fun s' ha hr => ?_
  have f := ha.frame
  rw [k₁.rsp, u₁.mem] at f
  refine hQ s' (k₁.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) (u₁.mem ▸ f) ?_) f hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact away_st hH hp hst (fun _ h => h)
  · exact away_stk hH hp (fun _ h => h)

end

/-! ## The padded keys -/

/-- The 128 bits whose low and high halves are both `c` (`Hash.padConst`). -/
def rep16 (c : BitVec 64) : BitVec 128 :=
  XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ c) ((0 : BitVec 64) ++ c)

theorem vbytes_ipad : vbytes (rep16 0x3636363636363636) = List.replicate 16 ipad := by decide

theorem vbytes_x6a : vbytes (rep16 0x6a6a6a6a6a6a6a6a) = List.replicate 16 (0x6a : Byte) := by decide

/-- A 16-byte store writes the register's bytes. -/
theorem store16 (m : Mem) (a : Addr) (v : BitVec 128) : m.writeW a v = writeBytes m a (vbytes v) :=
  Pbkdf2.Memory.writeW_bytes m a v _ (by simp only [Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]; rfl)

/-- The bytes of 16 bytes XORed with one byte repeated. -/
theorem vbytes_xor (x c : BitVec 128) (b : Byte) (h : vbytes c = List.replicate 16 b) :
    vbytes (x ^^^ c) = (vbytes x).map (· ^^^ b) := by
  apply List.ext_getElem (by simp only [vbytes_length, List.length_map])
  intro i h₁ h₂
  have hi : i < 16 := by rwa [vbytes_length] at h₁
  have hc : byte c i = b := by
    rw [← vbytes_getElem c (i := i) (by rwa [vbytes_length])]
    simp only [h, List.getElem_replicate]
  rw [List.getElem_map, vbytes_getElem, vbytes_getElem, ← hc]
  exact BitVec.extractLsb'_xor

/-- The bytes of 16 bytes loaded from memory. -/
theorem vbytes_readW (m : Mem) (a : Addr) : vbytes (m.readW a 128) = bytesAt m a 16 := by
  simp only [vbytes, bytesAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [byte, Mem.readW, BitVec.setWidth_eq]
  exact extractLsb'_read _ _ hj

/-- Bytes written inside bytes written before: those, in place. -/
theorem writeBytes_over (m : Mem) (q : Addr) (xs ys zs : List Byte) {j : Nat}
    (hx : xs.length < 2 ^ 63) (hy : j + ys.length ≤ xs.length) (hz : zs.length = xs.length)
    (h : ∀ i < xs.length, zs.getD i 0 = if j ≤ i ∧ i < j + ys.length then ys.getD (i - j) 0 else xs.getD i 0) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 j) ys = writeBytes m q zs := by
  funext a
  have hd := (a - q).isLt
  simp only [writeBytes, Offset.sub_add_eq, Offset.toNat_sub_ofNat, hz]
  generalize (a - q).toNat = d at hd ⊢
  rw [Nat.mod_eq_of_lt (a := j) (by omega_using [hx, hy])]
  by_cases hdj : j ≤ d
  · rw [show 2 ^ 64 - j + d = (d - j) + 2 ^ 64 by omega_using [hd, hdj], Nat.add_mod_right, Nat.mod_eq_of_lt (a := d - j) (by omega_using [hd])]
    by_cases hdx : d < xs.length
    · rw [ite_eq_left hdx, ite_eq_left hdx, h d hdx]
      by_cases hdy : d - j < ys.length
      · rw [ite_eq_left hdy, ite_eq_left ⟨hdj, by omega_using [hdy]⟩]
      · rw [ite_eq_right hdy, ite_eq_right (by omega_using [hdy])]
    · rw [ite_eq_right hdx, ite_eq_right hdx, ite_eq_right (by omega_using [hy, hdx])]
  · rw [Nat.mod_eq_of_lt (a := 2 ^ 64 - j + d) (by omega_using [hd, hdj]), ite_eq_right (by omega_using [hx, hy])]
    by_cases hdx : d < xs.length
    · rw [ite_eq_left hdx, ite_eq_left hdx, h d hdx, ite_eq_right (by omega_using [hdj])]
    · rw [ite_eq_right hdx, ite_eq_right hdx]

/-- Sixteen more bytes of the key. -/
theorem ipadBlk_add16 (m mk : Mem) (P K : Addr) {B j : Nat} (v : BitVec 128) (hB : B < 2 ^ 63) (hj : j + 16 ≤ B)
    (hv : vbytes v = (bytesAt mk (K + BitVec.ofNat 64 j) 16).map (· ^^^ ipad)) :
    (writeBytes m P (ipadBlk mk K B j)).writeW (P + BitVec.ofNat 64 j) v = writeBytes m P (ipadBlk mk K B (j + 16)) := by
  have hl : ((bytesAt mk (K + BitVec.ofNat 64 j) 16).map (· ^^^ ipad)).length = 16 := by
    rw [List.length_map, bytesAt_length]
  rw [store16, hv]
  refine writeBytes_over _ _ _ _ _ (by rw [ipadBlk_length]; exact hB) (by rw [ipadBlk_length, hl]; exact hj)
    (by rw [ipadBlk_length, ipadBlk_length]) fun i hi => ?_
  rw [ipadBlk_length] at hi
  rw [hl]
  simp only [ipadBlk, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  by_cases hi' : j ≤ i ∧ i < j + 16
  · rw [ite_eq_left hi', List.getElem?_range (by omega_using [hi']), ite_eq_left hi'.2]
    simp only [Option.map_some, Option.getD_some]
    rw [add_ofNat, show j + (i - j) = i by omega_using [hi']]
  · rw [ite_eq_right hi']
    by_cases hij : i < j
    · rw [ite_eq_left hij, ite_eq_left (by omega_using [hij])]
    · rw [ite_eq_right hij, ite_eq_right (by omega_using [hi', hij])]

/-- One more 16 bytes of the outer buffer, after `16 n` of them: the inner
buffer's, XORed with `0x6a` in every byte. -/
theorem xorOpad_mem16 (m : Mem) (A Q : Addr) (n : Nat) (c : BitVec 128) (hc : vbytes c = List.replicate 16 (0x6a : Byte))
    (hsep : Mem.Sep A (16 * n + 16) Q (16 * n + 16)) (hlt : 16 * n + 16 < 2 ^ 64) :
    (writeBytes m Q ((bytesAt m A (16 * n)).map (· ^^^ 0x6a))).writeW (Q + BitVec.ofNat 64 (16 * n))
      ((writeBytes m Q ((bytesAt m A (16 * n)).map (· ^^^ 0x6a))).readW (A + BitVec.ofNat 64 (16 * n)) 128 ^^^ c) =
      writeBytes m Q ((bytesAt m A (16 * n + 16)).map (· ^^^ 0x6a)) := by
  have hl : ((bytesAt m A (16 * n)).map (· ^^^ (0x6a : Byte))).length = 16 * n := by
    rw [List.length_map, bytesAt_length]
  rw [store16, vbytes_xor _ _ _ hc, vbytes_readW, bytesAt_writeBytes_sep]
  · rw [bytesAt_add, List.map_append]
    exact Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [hl])
      (by rw [hl, List.length_map, bytesAt_length]; exact hlt)
  · intro x hx hy
    rw [hl] at hy
    apply hsep x _ (by omega_using [hy])
    rw [show x - A = (x - (A + BitVec.ofNat 64 (16 * n))) + BitVec.ofNat 64 (16 * n) by
        rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * n) (by omega_using [hlt])]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (16 * n))).toNat + 16 * n) (2 ^ 64)
    omega_using [hx]
  · omega_using []

theorem mask64 : ∀ j < 4, BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (64 - 16)).signExtend 64 =
    BitVec.ofNat 64 (16 * j) := by decide

theorem mask128 : ∀ j < 8, BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (128 - 16)).signExtend 64 =
    BitVec.ofNat 64 (16 * j) := by decide

/-- The 16-byte key loop's index, clamped to the block, is itself. -/
theorem and_mask16 {B : Nat} (hB : B = 64 ∨ B = 128) {j : Nat} (hj : 16 * j + 16 ≤ B) :
    BitVec.ofNat 64 (16 * j) &&& (BitVec.ofNat 32 (B - 16)).signExtend 64 = BitVec.ofNat 64 (16 * j) := by
  rcases hB with rfl | rfl
  · exact mask64 j (by omega_using [hj])
  · exact mask128 j (by omega_using [hj])

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := x.isLt; omega_using [])]

theorem ea_keyAt (s : State) : s.ea H.keyAt = s.gpr .rbx + BitVec.ofNat 64 H.P.N + s.gpr .r10 := by
  simp only [State.ea, Hash.keyAt, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-! The instructions of the key setup, with what they keep of the SSE
registers. -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movX {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_mov32iX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_andiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_subiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v.signExtend 64) → s'.xmm = s.xmm →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl rfl)

/-- Sixteen bytes loaded into `d` and XORed with `c`. -/
theorem wp_loadXor {d c : XReg} {m : MemOp} {a : Addr} (hdc : ¬c = d) (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.xmm d = s.mem.readW a 128 ^^^ s.xmm c → (∀ y, ¬y = d → s'.xmm y = s.xmm y) → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquLoad d m :: .xop (.bin .pxor d c) :: is)) s Q := by
  refine WP.cons (s' := s.setXmm d (s.mem.readW a 128)) (by simp [exec, State.load128, ha, hin])
    (wp_xbin (k _ rfl rfl rfl rfl ?_ fun y hy => ?_))
  · rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hdc]; rfl
  · rw [RegUpd.xmm_setXmm_of_ne _ _ hy, RegUpd.xmm_setXmm_of_ne _ _ hy]

/-- `Hash.padConst`: `c` in both halves of `x`, through `rax`. -/
theorem padConst_ok {x : XReg} {c : BitVec 64} {rest : List Instr}
    (k : ∀ s', (∀ r, ¬r = .rax → s'.gpr r = s.gpr r) → s'.xmm x = rep16 c →
      (∀ y, ¬y = x → s'.xmm y = s.xmm y) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (Hash.padConst x c ++ rest)) s Q := by
  simp only [Hash.padConst, List.cons_append, List.nil_append]
  refine wp_movImm64' (wp_movqx (wp_xbin (k _ (fun r h => ?_) ?_ (fun y h => ?_) rfl rfl rfl)))
  · rw [RegUpd.gpr_setXmm, RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne _ _ h]
  · rw [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self, RegUpd.gpr_setReg_self]; rfl
  · rw [RegUpd.xmm_setXmm_of_ne _ _ h, RegUpd.xmm_setXmm_of_ne _ _ h]; rfl

end

/-- Stores of `xmm0`, `ipad` in every byte, at `rbx + o + 16 k`, for `k < n`,
which write `16 n` bytes of `ipad` from `p = rbx + o`. -/
theorem fill_ok {o : Nat} {p : Addr} : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr .rbx + BitVec.ofNat 64 o = p → vbytes (s.xmm .xmm0) = List.replicate 16 ipad →
    (∀ k < n, InRegions s.wr (p + BitVec.ofNat 64 (16 * k)) 16) → 16 * n + 16 < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      s'.mem = writeBytes s.mem p (List.replicate (16 * n) ipad) → WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).map (fun k => Instr.movdquStore (at_ .rbx (o + 16 * k)) .xmm0) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [writeBytes_nil])
  | succ n ih =>
    intro rest s Q hp hx hout hn k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hp hx (fun j hj => hout j (by omega_using [hj])) (by omega_using [hn]) fun s₁ g₁ rd₁ wr₁ x₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_movdquStoreX (a := p + BitVec.ofNat 64 (16 * n)) (by rw [ea_off, g₁, hp])
      (by rw [wr₁]; exact hout n (by omega_using [])) fun s₂ g₂ m₂ rd₂ wr₂ x₂ =>
        k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [x₂, x₁]) ?_
    rw [m₂, m₁, x₁, store16, hx,
      Pbkdf2.Memory.writeBytes_append' _ _ _ (by rw [List.length_replicate])
        (by simp only [List.length_replicate]; omega_using [hn]),
      List.replicate_append_replicate, Nat.mul_succ]

/-- After `j` bytes of the key at `K` (whose bytes are those of `mk`), from the
state `s` the loops start in: the buffer at `P` holds `ipadBlk … j` over `m`. -/
structure KeyInv (s : State) (m mk : Mem) (P K : Addr) (B j : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  mem : t.mem = writeBytes m P (ipadBlk mk K B j)

/-- Where the key loops read and write. -/
structure KeyRegs (H : Hash) (s : State) (m mk : Mem) (P K : Addr) (kl : Nat) : Prop where
  kl_le : kl ≤ H.P.B
  hB : H.P.B = 64 ∨ H.P.B = 128
  rbp : s.gpr .rbp = K
  rbx : s.gpr .rbx + BitVec.ofNat 64 H.P.N = P
  r13 : s.gpr .r13 = BitVec.ofNat 64 kl
  key : ∀ i < kl, m (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i)
  kin : ∀ i n, i + n ≤ kl → InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 i) n
  bout : ∀ i n, i + n ≤ H.P.B → InRegions s.wr (P + BitVec.ofNat 64 i) n
  disj : Region.Disjoint ⟨K, kl⟩ ⟨P, H.P.B⟩

/-- The key's bytes are still where they were. -/
theorem KeyInv.key {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    {t : State} (h : KeyInv s m mk P K H.P.B j t) {i : Nat} (hi : i < kl) :
    t.mem (K + BitVec.ofNat 64 i) = mk (K + BitVec.ofNat 64 i) := by
  have hkl := hr.kl_le
  have hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  rw [h.mem, ← hr.key i hi]
  refine (writeBytes_frame m P _ (R := ⟨P, H.P.B⟩) (by rw [hl]; exact Region.contains_self _ _)).bytes
    (R := ⟨K, kl⟩) ?_ (by show kl ≤ 2 ^ 64; omega_using [hkl, hB]) hi
  simp only [List.mem_singleton]; rintro r rfl; exact hr.disj

theorem key_step16 {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (hx0 : vbytes (s.xmm .xmm0) = List.replicate 16 ipad) {j : Nat} (hj : j < kl / 16) {t : State}
    (h : KeyInv s m mk P K H.P.B (16 * j) t) (hx : t.xmm .xmm0 = s.xmm .xmm0)
    (hc : t.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j)) :
    WP isa (.block [.movdquLoad .xmm1 (byteAt .rbp 0), .xop (.bin .pxor .xmm1 .xmm0),
      .mov .r10 (.reg .r14), .alu .and .r10 (.imm (BitVec.ofNat 32 (H.P.B - 16))),
      .movdquStore H.keyAt .xmm1, .alu .add .r14 (.imm 16), .alu .sub .rcx (.imm 1)]) t
      fun t' => (KeyInv s m mk P K H.P.B (16 * (j + 1)) t' ∧ t'.xmm .xmm0 = s.xmm .xmm0 ∧
        t'.gpr .rcx = BitVec.ofNat 64 (kl / 16 - (j + 1))) ∧ t'.zf = some (decide (j + 1 = kl / 16)) := by
  have hkl := hr.kl_le
  have hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  have hj16 : 16 * j + 16 ≤ kl := by omega_using [hj]
  refine wp_loadXor (a := K + BitVec.ofNat 64 (16 * j)) (by decide)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbp,
      BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin _ 16 hj16) fun t₀ g₀ m₀ rd₀ wr₀ x₀ xo₀ => ?_
  refine wp_movX fun t₁ u₁ x₁ => wp_andiX fun t₂ u₂ x₂ => ?_
  have h10 : t₂.gpr .r10 = BitVec.ofNat 64 (16 * j) := by
    rw [u₂.gpr, u₁.gpr, g₀, h.r14, and_mask16 hr.hB (by omega_using [hj, hkl])]
  refine wp_movdquStoreX (a := P + BitVec.ofNat 64 (16 * j))
    (by rw [ea_keyAt, h10, u₂.other _ (by decide), u₁.other _ (by decide), g₀,
      h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbx])
    (by rw [u₂.wr, u₁.wr, wr₀, h.wr]; exact hr.bout _ 16 (by omega_using [hj, hkl])) fun t₃ g₃ m₃ rd₃ wr₃ x₃ => ?_
  refine wp_addiX fun t₄ u₄ x₄ => wp_subiX fun t₅ u₅ x₅ z₅ => WP.block_nil ?_
  have hv : vbytes (t.mem.readW (K + BitVec.ofNat 64 (16 * j)) 128 ^^^ t.xmm .xmm0) =
      (bytesAt mk (K + BitVec.ofNat 64 (16 * j)) 16).map (· ^^^ ipad) := by
    rw [vbytes_xor _ _ _ (by rw [hx]; exact hx0), vbytes_readW]
    congr 1
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [add_ofNat]
    exact h.key hr (by omega_using [hj, hi])
  have c₄ : t₄.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j) := by
    rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), u₁.other _ (by decide), g₀, hc]
  refine ⟨⟨⟨by rw [u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, rd₀, h.rd], by rw [u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, wr₀, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [u₅.other r h4, u₄.other r h2, g₃, u₂.other r h3, u₁.other r h3, g₀, h.other r h1 h2 h3 h4],
    by rw [u₅.other _ (by decide), u₄.gpr, g₃, u₂.other _ (by decide), u₁.other _ (by decide), g₀, h.r14,
      show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add, Nat.mul_succ], ?_⟩,
    by rw [x₅, x₄, x₃, x₂, x₁, xo₀ _ (by decide), hx], ?_⟩, ?_⟩
  · rw [u₅.mem, u₄.mem, m₃, x₂, x₁, x₀, u₂.mem, u₁.mem, m₀]
    generalize t.mem.readW (K + BitVec.ofNat 64 (16 * j)) 128 ^^^ t.xmm .xmm0 = v at hv ⊢
    rw [h.mem, ipadBlk_add16 _ _ _ _ _ (by omega_using [hB]) (by omega_using [hj, hkl]) hv, Nat.mul_succ]
  · rw [u₅.gpr, c₄, sx_one, ofNat_pred (by omega_using [hj])]; rfl
  · rw [z₅, c₄, sx_one, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (by omega_using [hkl, hB]) (by omega_using [])]
    exact congrArg some (decide_eq_decide.mpr (by omega_using []))

/-- The 16-byte key loop, skipped for a key shorter than that. -/
theorem key16_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl)
    (hx0 : vbytes (s.xmm .xmm0) = List.replicate 16 ipad) (h14 : s.gpr .r14 = BitVec.ofNat 64 0)
    (hc : s.gpr .rcx = BitVec.ofNat 64 (kl / 16)) (hz : s.zf = some (decide (kl / 16 = 0)))
    (hm : s.mem = writeBytes m P (ipadBlk mk K H.P.B 0)) :
    WP isa (.ite .e (.block []) H.keyLoop16) s (KeyInv s m mk P K H.P.B (16 * (kl / 16))) := by
  have i0 : KeyInv s m mk P K H.P.B (16 * 0) s := ⟨rfl, rfl, fun _ _ _ _ _ => rfl, h14, hm⟩
  refine WP.ite (decide (kl / 16 = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : kl / 16 = 0 := by simpa using h0
    rw [this]; exact i0
  · have : 0 < kl / 16 := by simp at h0; omega_using [h0]
    exact WP.mono (count_loop this
      (fun j t => KeyInv s m mk P K H.P.B (16 * j) t ∧ t.xmm .xmm0 = s.xmm .xmm0 ∧
        t.gpr .rcx = BitVec.ofNat 64 (kl / 16 - j))
      (fun j hj t h => key_step16 hr hx0 hj h.1 h.2.1 h.2.2) ⟨i0, rfl, hc⟩) fun t ht => ht.1

theorem key_step {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j : Nat}
    (hj : j < kl) {t : State} (h : KeyInv s m mk P K H.P.B j t) :
    WP isa (.block [.movzx8 .rax (byteAt .rbp 0), .alu32 .xor .rax (.imm 0x36),
      .mov .r10 (.reg .r14), .alu .and .r10 (.imm (BitVec.ofNat 32 (H.P.B - 1))),
      .store8 H.keyAt .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) t
      fun t' => KeyInv s m mk P K H.P.B (j + 1) t' ∧ t'.zf = some (decide (j + 1 = kl)) := by
  have hkl := hr.kl_le
  have hB : H.P.B ≤ 128 := by rcases hr.hB with h | h <;> omega_using [h]
  have hl : (ipadBlk mk K H.P.B j).length = H.P.B := ipadBlk_length _ _ _ _
  have hbyte : t.mem (K + BitVec.ofNat 64 j) = mk (K + BitVec.ofNat 64 j) := h.key hr hj
  refine wp_movzx8 (a := K + BitVec.ofNat 64 j)
    (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbp,
      BitVec.add_zero])
    (by rw [h.rd, h.wr]; exact hr.kin j 1 hj) fun t₁ u₁ => ?_
  refine wp_xor32i fun t₂ u₂ => wp_mov fun t₃ u₃ _ _ => wp_andi fun t₄ u₄ => ?_
  have h10 : t₄.gpr .r10 = BitVec.ofNat 64 j := by
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r14, and_mask hr.hB,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_using [hj, hkl, hB]),
      Nat.mod_eq_of_lt (by omega_using [hj, hkl])]
  refine wp_store8 (a := P + BitVec.ofNat 64 j)
    (by rw [ea_keyAt, h10, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide) (by decide), hr.rbx])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hr.bout j 1 (by omega_using [hj, hkl]))
    fun t₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_addi fun t₆ u₆ => wp_cmp fun t₇ g₇ m₇ rd₇ wr₇ _ z₇ => WP.block_nil ?_
  have h14 : t₆.gpr .r14 = BitVec.ofNat 64 (j + 1) := by
    rw [u₆.gpr, g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.r14, sx_one, ofNat_succ]
  refine ⟨⟨by rw [rd₇, u₆.rd, rd₅, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [wr₇, u₆.wr, wr₅, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    fun r h1 h2 h3 h4 => by
      rw [g₇, u₆.other r h2, g₅, u₄.other r h3, u₃.other r h3, u₂.other r h1, u₁.other r h1,
        h.other r h1 h2 h3 h4],
    by rw [g₇, h14], ?_⟩, ?_⟩
  · have v : (t₄.gpr .rax).setWidth 8 = mk (K + BitVec.ofNat 64 j) ^^^ ipad := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, xor_byte, hbyte]; rfl
    rw [m₇, u₆.mem, m₅, v, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem,
      writeBytes_set _ _ _ (by rw [hl]; omega_using [hj, hkl]) (by rw [hl]; omega_using [hB]), ipadBlk_succ]
  · rw [z₇, h14, show t₆.gpr .r13 = BitVec.ofNat 64 kl by
      rw [u₆.other _ (by decide), g₅, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.other _ (by decide) (by decide) (by decide) (by decide), hr.r13],
      sub_beq (by omega_using [hj, hkl, hB]) (by omega_using [hkl, hB])]

/-- The byte loop over the rest of the key, skipped when there is none. -/
theorem key_ok {s : State} {m mk : Mem} {P K : Addr} {kl : Nat} (hr : KeyRegs H s m mk P K kl) {j₀ : Nat}
    (hj₀ : j₀ ≤ kl) {t : State} (h : KeyInv s m mk P K H.P.B j₀ t) (hz : t.zf = some (decide (j₀ = kl))) :
    WP isa (.ite .e (.block []) H.keyLoop) t (KeyInv s m mk P K H.P.B kl) := by
  refine WP.ite (decide (j₀ = kl)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have : j₀ = kl := by simpa using h0
    rw [← this]; exact h
  · have hlt : 0 < kl - j₀ := by simp at h0; omega_using [h0, hj₀]
    have e : j₀ + (kl - j₀) = kl := by omega_using [hj₀]
    have := count_loop hlt (fun k t => KeyInv s m mk P K H.P.B (j₀ + k) t)
      (fun k hk t h => WP.mono (key_step hr (j := j₀ + k) (by omega_using [hk, hj₀]) h) fun t' ht' =>
        ⟨ht'.1, by rw [ht'.2]; exact congrArg some (decide_eq_decide.mpr (by omega_using [hk, hj₀]))⟩) h
    rwa [e] at this

/-- The 16-byte words of the outer buffer: `n` words of the inner buffer at
`rbx + N`, XORed with `xmm1`, `ipad ⊕ opad` in every byte, to `r12 + N`. -/
theorem opad_ok : ∀ n (rest : List Instr) (s : State) (Q : State → Prop),
    vbytes (s.xmm .xmm1) = List.replicate 16 (0x6a : Byte) →
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < n, InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * k)) 16) →
    Mem.Sep (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (16 * n) (s.gpr .r12 + BitVec.ofNat 64 H.P.N) (16 * n) →
    16 * n < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.xmm .xmm1 = s.xmm .xmm1 →
      s'.mem = writeBytes s.mem (s.gpr .r12 + BitVec.ofNat 64 H.P.N)
        ((bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 H.P.N) (16 * n)).map (· ^^^ 0x6a)) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap H.opadW ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ _ k
    exact k s rfl rfl rfl rfl (by simp [bytesAt, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hx hin hout hsep hlt k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q hx (fun j hj => hin j (by omega_using [hj])) (fun j hj => hout j (by omega_using [hj]))
      (fun x hx hy => hsep x (by omega_using [hx]) (by omega_using [hy])) (by omega_using [hlt])
      fun s₁ g₁ rd₁ wr₁ x₁ m₁ => ?_
    simp only [Hash.opadW, List.cons_append, List.nil_append]
    refine wp_loadXor (a := s.gpr .rbx + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * n)) (by decide)
      (by rw [ea_off, g₁]) (by rw [rd₁, wr₁]; exact hin n (by omega_using [])) fun s₂ g₂ m₂ rd₂ wr₂ x₂ xo₂ => ?_
    refine wp_movdquStoreX (a := s.gpr .r12 + BitVec.ofNat 64 H.P.N + BitVec.ofNat 64 (16 * n))
      (by rw [ea_off, g₂, g₁]) (by rw [wr₂, wr₁]; exact hout n (by omega_using []))
      fun s₃ g₃ m₃ rd₃ wr₃ x₃ => k s₃ (by rw [g₃, g₂, g₁]) (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁])
        (by rw [x₃, xo₂ _ (by decide), x₁]) ?_
    rw [m₃, x₂, m₂, m₁, x₁, Nat.mul_succ,
      xorOpad_mem16 _ _ _ _ _ hx (by rwa [← Nat.mul_succ]) (by omega_using [hlt])]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- `K₀ ⊕ ipad` into the inner buffer and `K₀ ⊕ opad` into the outer one, and
the inner block's address in `rsi`. -/
theorem keys_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa H.initKeys s fun t => KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀) ∧
      Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem t.mem ∧
      bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad ∧
      bytesAt t.mem (bufOf H (out s₀)) H.P.B = xorPad (k0 H s₀) opad := by
  obtain ⟨hN4, hB4, hN, hB0, hB, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have hd := hH.dims.B
  have eB : 16 * (H.P.B / 16) = H.P.B := by rcases hd with h | h <;> omega_using [h]
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ ⟨inn s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ ⟨out s₀, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hS : H.S = H.P.N + H.P.B := rfl
  have inI : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (inn s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, si.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega_using [hS, hn]) (by omega_using [hN, hB, hn])⟩
  have inO : ∀ i n, i + n ≤ H.P.B → InRegions s₀.wr (bufOf H (out s₀) + BitVec.ofNat 64 i) n :=
    fun i n hn => ⟨_, so.mem, by rw [add_ofNat]; exact Offset.contains_base _ (by omega_using [hS, hn]) (by omega_using [hN, hB, hn])⟩
  have dIO : Region.Disjoint ⟨bufOf H (inn s₀), H.P.B⟩ ⟨bufOf H (out s₀), H.P.B⟩ :=
    (hp.i_o.sub_left bI).sub_right bO
  unfold Hash.initKeys Hash.ipadFill
  rw [List.append_assoc]
  refine WP.seq (padConst_ok fun s₁ g₁ x₁ xo₁ m₁ rd₁ wr₁ => ?_)
  refine fill_ok (o := H.P.N) (p := bufOf H (inn s₀)) (H.P.B / 16) _ s₁ _ (by rw [g₁ _ (by decide), hk.rbx])
    (by rw [x₁]; exact vbytes_ipad) (fun k hk' => by rw [wr₁, hk.wr]; exact inI _ 16 (by omega_using [hk', eB]))
    (by omega_using [hB]) fun s₂ g₂ rd₂ wr₂ x₂ m₂ => ?_
  refine wp_mov32iX fun s₃ u₃ x₃ => wp_movX fun s₄ u₄ x₄ => wp_shrX (by decide) fun s₆ u₅ x₆ =>
    wp_testX fun s₅ g₆ m₆ rd₆ wr₆ xt₆ z₅ => WP.block_nil ?_
  have G₅ : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .rcx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [g₆, u₅.other r h3, u₄.other r h3, u₃.other r h2, g₂, g₁ r h1]
  have rd₅ : s₅.rd = s₀.rd := by rw [rd₆, u₅.rd, u₄.rd, u₃.rd, rd₂, rd₁, hk.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [wr₆, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁, hk.wr]
  have r13₄ : s₃.gpr .r13 = s₀.gpr .rcx := by
    rw [u₃.other _ (by decide), g₂, g₁ _ (by decide), hk.r13]
  have hr : KeyRegs H s₅ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) (kl s₀) :=
    { kl_le := hkl, hB := hd
      rbp := by rw [G₅ _ (by decide) (by decide) (by decide), hk.rbp]
      rbx := by rw [G₅ _ (by decide) (by decide) (by decide), hk.rbx]
      r13 := by rw [G₅ _ (by decide) (by decide) (by decide), hk.r13, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      key := hk.key
      kin := fun i n hi => by
        rw [rd₅, wr₅, hp.rd]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
          Offset.contains_base _ (by omega_using [hi]) (by omega_using [hB, hkl, hi])⟩
      bout := fun i n hi => by rw [wr₅]; exact inI i n hi
      disj := hp.k_i.sub_right bI }
  have hx0 : vbytes (s₅.xmm .xmm0) = List.replicate 16 ipad := by
    rw [xt₆, x₆, x₄, x₃, x₂, x₁]; exact vbytes_ipad
  have h14 : s₅.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]; rfl
  have hc : s₅.gpr .rcx = BitVec.ofNat 64 (kl s₀ / 16) := by rw [g₆, u₅.gpr, u₄.gpr, r13₄, shr4]
  have hz : s₅.zf = some (decide (kl s₀ / 16 = 0)) := by
    rw [z₅, BitVec.and_self, u₅.gpr, u₄.gpr, r13₄, shr4, ofNat_beq_zero (by omega_using [hkl, hB])]
  have hm : s₅.mem = writeBytes s.mem (bufOf H (inn s₀)) (ipadBlk s₀.mem (kp s₀) H.P.B 0) := by
    rw [m₆, u₅.mem, u₄.mem, u₃.mem, m₂, m₁, ipadBlk_zero, eB]
  refine WP.seq (WP.mono (key16_ok hr hx0 h14 hc hz hm) fun t₆ h₆ => ?_)
  refine WP.seq (wp_cmp fun t₇ g₇ m₇ rd₇ wr₇ _ z₇ => WP.block_nil ?_)
  have h₇ : KeyInv s₅ s.mem s₀.mem (bufOf H (inn s₀)) (kp s₀) H.P.B (16 * (kl s₀ / 16)) t₇ :=
    ⟨by rw [rd₇, h₆.rd], by rw [wr₇, h₆.wr], fun r h1 h2 h3 h4 => by rw [g₇, h₆.other r h1 h2 h3 h4],
      by rw [g₇, h₆.r14], by rw [m₇, h₆.mem]⟩
  have hz₇ : t₇.zf = some (decide (16 * (kl s₀ / 16) = kl s₀)) := by
    rw [z₇, h₆.r14, h₆.other _ (by decide) (by decide) (by decide) (by decide), hr.r13,
      sub_beq (by omega_using [hkl, hB]) (by omega_using [hkl, hB])]
  refine WP.seq (WP.mono (key_ok hr (by omega_using []) h₇ hz₇) fun t ht => ?_)
  have Gt : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → t.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [ht.other r h1 h2 h3 h4, G₅ r h1 h2 h4]
  have bxt : t.gpr .rbx = inn s₀ := by rw [Gt _ (by decide) (by decide) (by decide) (by decide), hk.rbx]
  have r12t : t.gpr .r12 = out s₀ := by rw [Gt _ (by decide) (by decide) (by decide) (by decide), hk.r12]
  have rdt : t.rd = s₀.rd := by rw [ht.rd, rd₅]
  have wrt : t.wr = s₀.wr := by rw [ht.wr, wr₅]
  unfold Hash.opadFill
  rw [List.append_assoc]
  refine padConst_ok fun s₈ g₈ x₈ xo₈ m₈ rd₈ wr₈ => ?_
  have bx₈ : s₈.gpr .rbx = inn s₀ := by rw [g₈ _ (by decide), bxt]
  have r12₈ : s₈.gpr .r12 = out s₀ := by rw [g₈ _ (by decide), r12t]
  refine opad_ok (H.P.B / 16) _ s₈ _ (by rw [x₈]; exact vbytes_x6a)
    (fun k hk' => by rw [bx₈, rd₈, wr₈, rdt, wrt]; exact InRegions.right' (inI _ 16 (by omega_using [hk', eB])))
    (fun k hk' => by rw [r12₈, wr₈, wrt]; exact inO _ 16 (by omega_using [hk', eB]))
    (by rw [bx₈, r12₈, eB]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by omega_using [hB])
    fun s₉ g₉ rd₉ wr₉ _ m₉ => ?_
  refine wp_mov fun s₁₀ u₁₀ _ _ => wp_addi fun s₁₁ u₁₁ => WP.block_nil ?_
  rw [bx₈, r12₈, eB, m₈] at m₉
  have G : ∀ r, r ≠ .rax → r ≠ .r14 → r ≠ .r10 → r ≠ .rcx → r ≠ .rsi → s₁₁.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [u₁₁.other r h5, u₁₀.other r h5, g₉, g₈ r h1, Gt r h1 h2 h3 h4]
  have hm' : s₁₁.mem = s₉.mem := by rw [u₁₁.mem, u₁₀.mem]
  have lI : (ipadBlk s₀.mem (kp s₀) H.P.B (kl s₀)).length = H.P.B := ipadBlk_length _ _ _ _
  have bt : bytesAt t.mem (bufOf H (inn s₀)) H.P.B = xorPad (k0 H s₀) ipad := by
    rw [ht.mem, bytesAt_writeBytes_self' lI (by omega_using [hB]), ipadBlk_eq _ _ hkl]
  have lO : ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length = H.P.B := by
    simp [bytesAt]
  have fT : Frame [⟨bufOf H (inn s₀), H.P.B⟩] s.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lI]; exact Region.contains_self _ _)
  have f₉ : Frame [⟨bufOf H (out s₀), H.P.B⟩] t.mem s₉.mem := by
    rw [m₉]; exact writeBytes_frame _ _ _ (by rw [lO]; exact Region.contains_self _ _)
  have f : Frame [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] s.mem s₁₁.mem := by
    rw [hm']; exact (fT.mono (by simp)).trans (f₉.mono (by simp))
  refine ⟨hk.keep (by rw [u₁₁.rd, u₁₀.rd, rd₉, rd₈, rdt, hk.rd]) (by rw [u₁₁.wr, u₁₀.wr, wr₉, wr₈, wrt, hk.wr])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact G _ (by decide) (by decide) (by decide) (by decide) (by decide)) f
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact away_st hH hp si bI
        · exact away_st hH hp so bO),
    by rw [u₁₁.gpr, u₁₀.gpr, g₉, bx₈, sx_ofNat (by omega_using [hN])], f, ?_, ?_⟩
  · have sIO : Mem.Sep (bufOf H (inn s₀)) H.P.B (bufOf H (out s₀))
        ((bytesAt t.mem (bufOf H (inn s₀)) H.P.B).map (· ^^^ (0x6a : Byte))).length := by
      rw [lO]; exact dIO.sep (Region.contains_self _ _) (Region.contains_self _ _)
    rw [hm', m₉, bytesAt_writeBytes_sep _ _ sIO (by omega_using [hB]), bt]
  · rw [hm', m₉, bytesAt_writeBytes_self' lO (by omega_using [hB]), bt, xorOpad_ipad]

/-! ## The compressions -/

/-- What the call of the compression function needs, for the state at `p`. -/
theorem callOk {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hsi : t.gpr .rsi = bufOf H p) : CallOk H.P t p (scr s₀) (bufOf H p) := by
  obtain ⟨-, -, hN, -, hB, hso, -, -, hL, h8⟩ := sizes hH hp
  have sR : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hv : Region.Sub ⟨p, H.P.N⟩ ⟨p, H.S⟩ := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have hb : Region.Sub ⟨bufOf H p, H.P.B⟩ ⟨p, H.S⟩ := Offset.sub_base _ (Nat.le_refl _)
  have hc : Region.Sub ⟨scr s₀, H.P.so⟩ (scR sc s₀) := cal_sub hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine ⟨hk.rbx, hk.r15, hsi, (hs.sc.sub_left hv).sub_right hc,
    Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hN, hB]), (hs.sc.sub_left hb).sub_right hc,
    (hs.stk.sub_left b8).sub_right hv, (hp.stk_s.sub_left b8).sub_right hc,
    (hs.stk.sub_left b8).sub_right hb, ?_, ?_⟩
  · rw [hk.rd, hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_append_right _ hs.mem, H.P.N, rfl, by show H.P.N + H.P.B ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ hs.mem, 0, (BitVec.add_zero _).symm,
        by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, List.mem_append_right _ sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hso, hL]⟩
  · rw [hk.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hs.mem, 0, (BitVec.add_zero _).symm, by show 0 + H.P.N ≤ H.P.N + H.P.B; omega_using []⟩
    · exact ⟨_, sR, 0, (BitVec.add_zero _).symm, by show 0 + H.P.so ≤ 8 * sc; omega_using [hso, hL]⟩

/-- The compression of the block in the buffer of the state at `p` into its
hash value. -/
theorem cmp_ok {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) {t : State} (hk : KR H s₀ p t)
    (hsi : t.gpr .rsi = bufOf H p) {Q : State → Prop}
    (k : ∀ s', KR H s₀ p s' → Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem →
      hH.md.stateAt s'.mem p = hH.md.compress (hH.md.stateAt t.mem p) (hH.md.blockAt t.mem (bufOf H p)) →
      Q s') :
    WP isa (compressAt H.compN H.compC) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  refine compressAt_ok hH.md hH.comp (callOk hH hp hs hk hsi) (by omega_using [hB]) (by omega_using [hN])
    fun s' hrd hwr hcs hfr hst _ _ => ?_
  have f : Frame [⟨p, H.P.N⟩, calR H s₀, stkR s₀] t.mem s'.mem := hfr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨calR H s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, b8⟩
  refine k s' (hk.keep hrd hwr (fun r hr => hcs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_) f hst
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact away_st hH hp hs (Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using []))
  · exact away_cal hH hp
  · exact away_stk hH hp (fun _ h => h)

/-- From the inner state to the outer one. -/
theorem mid_ok {s : State} (hk : KR H s₀ (inn s₀) s) :
    WP isa (.block H.initOuter) s fun t => KR H s₀ (out s₀) t ∧ t.gpr .rsi = bufOf H (out s₀) ∧
      t.mem = s.mem := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  unfold Hash.initOuter
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => WP.block_nil ?_
  have G : ∀ r, r ≠ .rbx → r ≠ .rsi → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨by rw [u₃.rd, u₂.rd, u₁.rd, hk.rd], by rw [u₃.wr, u₂.wr, u₁.wr, hk.wr],
    by rw [G _ (by decide) (by decide), hk.rsp],
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r12],
    by rw [G _ (by decide) (by decide), hk.rbp], by rw [G _ (by decide) (by decide), hk.r12],
    by rw [G _ (by decide) (by decide), hk.r13], by rw [G _ (by decide) (by decide), hk.r15],
    by rw [hm]; exact hk.saved, by rw [hm]; exact hk.ret, fun i hi => by rw [hm]; exact hk.key i hi⟩,
    by rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r12, sx_ofNat (by omega_using [hN])], hm⟩

end

/-- What `init` needs of `H.compBoth`, the code compressing the blocks of
its two states: from the inner state at `rbx` with its block at `rsi`, both
hash values are compressed with the blocks in their buffers, and what the
prologue set up is kept (`rbx` may be either state); and it is constant
time. -/
structure BothOk (H : Hash) (hH : HashOK H) : Prop where
  ok : ∀ {sc : Nat} {s₀ : State}, Pre H sc s₀ → ∀ {t : State}, KR H s₀ (inn s₀) t →
    t.gpr .rsi = bufOf H (inn s₀) → ∀ {Q : State → Prop},
    (∀ s' b, KR H s₀ b s' →
      hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt t.mem (inn s₀)) (hH.md.blockAt t.mem (bufOf H (inn s₀))) →
      hH.md.stateAt s'.mem (out s₀) =
        hH.md.compress (hH.md.stateAt t.mem (out s₀)) (hH.md.blockAt t.mem (bufOf H (out s₀))) →
      Q s') → WP isa H.compBoth t Q
  rel : ∀ {sc : Nat} {s₀ s₀' : State}, Pre H sc s₀ → Pre H sc s₀' → PubEq s₀ s₀' →
    RelCT isa (fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀)))
      H.compBoth fun s s' => ∃ b, KR H s₀ b s ∧ KR H s₀' b s'

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- A hash value away from what was written is the same. -/
theorem stateAt_keep {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) : hH.md.stateAt m' p = hH.md.stateAt m p := by
  obtain ⟨-, -, hN, -⟩ := sizes hH hp
  exact hH.md.stateAt_congr fun i hi =>
    hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega_using [hN]) hi

/-- A block away from what was written is the same. -/
theorem blockAt_keep {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.P.B⟩ r) : hH.md.blockAt m' p = hH.md.blockAt m p := by
  obtain ⟨-, -, -, -, hB, -⟩ := sizes hH hp
  exact hH.md.parse_congr fun k hk =>
    hf.bytes (R := ⟨_, H.P.B⟩) hd (by show H.P.B ≤ 2 ^ 64; omega_using [hB]) hk

/-! ## Correctness -/

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = k0 H s₀ := by
  have := hp.kl_le
  simp only [blockKey, k0, K0, bytesAt_length, hH.hB, show ¬ (H.P.B < kl s₀) by omega_using [this], ↓reduceIte]

theorem correct (hbo : BothOk H hH) : WP isa H.hmacInit s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  obtain ⟨-, -, hN, hB0, hB, -, -, hW, hL, -⟩ := sizes hH hp
  have hkl := hp.kl_le
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have hsc : scR sc s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq (WP.mono (pro_ok hH hp) fun s₁ k₁ => ?_)
  refine WP.seq (callInit_ok hH hp k₁ (st := .rbx) k₁.rbx si fun s₂ k₂ f₂ r₂ => ?_)
  refine WP.seq (callInit_ok hH hp k₂ (st := .r12) k₂.r12 so fun s₃ k₃ f₃ r₃ => ?_)
  refine WP.seq (WP.mono (keys_ok hH hp k₃) fun s₄ ⟨k₄, si₄, f₄, bI₄, bO₄⟩ => ?_)
  refine WP.seq (hbo.ok hp k₄ si₄ fun s₇ b k₇ eI eO => ?_)
  refine WP.mono (restore_ok H.stream k₇.r15 hW k₇.saved (by rw [k₇.wr]; exact hsc) hL)
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₇.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₇.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  -- What each piece keeps: the hash values and the buffers it does not write.
  have keepS : ∀ {rs : List Region} {m m' : Mem} {p : Addr}, Frame rs m m' →
      (∀ r ∈ rs, Region.Disjoint ⟨p, H.P.N⟩ r) → hH.md.stateAt m' p = hH.md.stateAt m p :=
    fun hf hd => hH.md.stateAt_congr fun i hi =>
      hf.bytes (R := ⟨_, H.P.N⟩) hd (by show H.P.N ≤ 2 ^ 64; omega_using [hN]) hi
  have hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) := Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have nb : ∀ p : Addr, Region.Disjoint ⟨p, H.P.N⟩ ⟨bufOf H p, H.P.B⟩ := fun p =>
    Offset.base_disjoint _ (Nat.le_refl _) (by omega_using [hN, hB])
  have iv : ∀ {m : Mem} {p : Addr}, hH.SH.Repr m p [] → hH.md.stateAt m p = hH.iv := fun h => by
    have := ((hH.repr _ _ _).1 h).1
    rwa [List.length_nil, Nat.zero_div, Md.compressList_zero] at this
  -- The inner state.
  have iv₄ : hH.md.stateAt s₄.mem (inn s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact nb _
        · exact (hp.i_o.sub_left hvI).sub_right bO),
      keepS f₃ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.i_o.sub_left hvI
        · exact hp.stk_i.symm.sub_left hvI), iv r₂]
  have hl : (xorPad (k0 H s₀) ipad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rI := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl bI₄ (eI.trans (congrArg (hH.md.compress · _) iv₄))
  -- The outer state.
  have ivO₄ : hH.md.stateAt s₄.mem (out s₀) = hH.iv := by
    rw [keepS f₄ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact (hp.i_o.symm.sub_left hvO).sub_right bI
        · exact nb _), iv r₃]
  have hl' : (xorPad (k0 H s₀) opad).length = H.P.B := by
    rw [Proof.Hmac.Common.xorPad_length, K0_length _ _ hkl]
  have rO := Md.repr_block (H := hH.md) (iv := hH.iv) hB0 hl' bO₄ (eO.trans (congrArg (hH.md.compress · _) ivO₄))
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨(hH.repr _ _ _).2 rI, (hH.repr _ _ _).2 rO⟩

end

/-! ## Constant time -/

/-- The taint checks of the pieces of `init` between its calls. -/
structure Checks (H : Hash) : Prop where
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs args) (.block H.initPrologue) hc).isSome = true
  argI : ∀ st ∈ [Reg.rbx, .r12], ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block [.mov .rdi (.reg st)])
    hc).isSome = true
  keys : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) H.initKeys hc).isSome = true
  mid : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.initOuter) hc).isSome = true
  restore : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block H.stream.restore) hc).isSome = true

section
variable {sc : Nat} {s₀ s₀' : State} (hp : Pre H sc s₀) (hp' : Pre H sc s₀') (hq : PubEq s₀ s₀')

omit hH in
theorem kr_agree (hq : PubEq s₀ s₀') {b : Addr} {s s' : State} (h : KR H s₀ b s) (h' : KR H s₀' b s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]
  · rw [h.rbp, h'.rbp, kp, kp, hq.rdx]
  · rw [h.r12, h'.r12, out, out, hq.rsi]
  · rw [h.r13, h'.r13, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

/-- A call of the streaming `init` on the state at `p`, from `st`. -/
theorem callInit_rel (hc : Checks H) {b : Addr} {st : Reg} (hst : st ∈ [Reg.rbx, .r12]) {p : Addr}
    (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p) (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p)
    (hr : ∀ {t : State}, KR H s₀ b t → t.gpr st = p) (hr' : ∀ {t : State}, KR H s₀' b t → t.gpr st = p) :
    RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (H.stream.callInit st)
      fun s s' => KR H s₀ b s ∧ KR H s₀' b s' := by
  have ha : RelCT isa (fun s s' => KR H s₀ b s ∧ KR H s₀' b s') (.block [.mov .rdi (.reg st)])
      fun s s' => (KR H s₀ b s ∧ s.gpr .rdi = p) ∧ (KR H s₀' b s' ∧ s'.gpr .rdi = p) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') (hc.argI st hst)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr h]⟩)
      (fun _ h => wp_mov fun t u _ _ => WP.block_nil ⟨h.regs u.rd u.wr (fun r hr => u.other r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u.mem, by rw [u.gpr, hr' h]⟩)
  have call : ∀ {t₀ : State}, Pre H sc t₀ → StOk (H := H) (sc := sc) (s₀ := t₀) p → ∀ t, KR H t₀ b t →
      t.gpr .rdi = p → WP isa (.call H.stream.initN H.stream.initC) t (KR H t₀ b) := fun hpt hst t k d => by
    refine init_call hH.stream (st := p) d (by rw [k.wr]; exact covers_one hst.mem)
      (by rw [k.rsp]; exact hst.stk) fun s' ha _ => ?_
    have f := ha.frame
    rw [k.rsp] at f
    refine k.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact away_st hH hpt hst (fun _ h => h)
    · exact away_stk hH hpt (fun _ h => h)
  refine ha.seq (rel_wp (F := fun s => KR H s₀ b s ∧ s.gpr .rdi = p)
    (F' := fun s => KR H s₀' b s ∧ s.gpr .rdi = p) (init_rel hH.stream (st := p) fun s s' h => ?_)
    (fun t ⟨k, d⟩ => call hp hs t k d) (fun t ⟨k, d⟩ => call hp' hs' t k d))
  obtain ⟨⟨k, d⟩, ⟨k', d'⟩⟩ := h
  exact ⟨d, d', by rw [k.wr]; exact covers_one hs.mem, by rw [k'.wr]; exact covers_one hs'.mem,
    by rw [k.rsp]; exact hs.stk, by rw [k'.rsp]; exact hs'.stk, by rw [k.rsp, k'.rsp, hq.rsp]⟩

/-- A compression of the state at `p`. -/
theorem cmp_rel {p : Addr} (hs : StOk (H := H) (sc := sc) (s₀ := s₀) p)
    (hs' : StOk (H := H) (sc := sc) (s₀ := s₀') p) :
    RelCT isa (fun s s' => (KR H s₀ p s ∧ s.gpr .rsi = bufOf H p) ∧ (KR H s₀' p s' ∧ s'.gpr .rsi = bufOf H p))
      (compressAt H.compN H.compC) fun s s' => KR H s₀ p s ∧ KR H s₀' p s' :=
  rel_wp (compressAt_rel hH.md hH.comp fun s s' ⟨⟨k, si⟩, ⟨k', si'⟩⟩ =>
      ⟨⟨_, _, _, callOk hH hp hs k si⟩, ⟨_, _, _, callOk hH hp' hs' k' si'⟩,
        by rw [k.rbx, k'.rbx], by rw [k.r15, k'.r15, scr, scr, hq.r8], by rw [si, si'],
        by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun s ⟨k, si⟩ => cmp_ok hH hp hs k si fun s' k' _ _ => k')
    (fun s ⟨k, si⟩ => cmp_ok hH hp' hs' k si fun s' k' _ _ => k')

/-- From the inner state to the outer one. -/
theorem mid_rel (hc : Checks H) :
    RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') (.block H.initOuter)
      fun s s' => (KR H s₀ (out s₀) s ∧ s.gpr .rsi = bufOf H (out s₀)) ∧
        (KR H s₀' (out s₀) s' ∧ s'.gpr .rsi = bufOf H (out s₀)) := by
  have ei : inn s₀' = inn s₀ := hq.rdi.symm
  have eo : out s₀' = out s₀ := hq.rsi.symm
  exact rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.mid
    (fun _ h => WP.mono (mid_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ h => WP.mono (mid_ok hH hp' (ei ▸ h)) fun _ h => ⟨eo ▸ h.1, by rw [h.2.1, eo]⟩)

theorem ct (hbo : BothOk H hH) (hc : Checks H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.hmacInit fun _ _ => True := by
  have ei : inn s₀' = inn s₀ := hq.rdi.symm
  have eo : out s₀' = out s₀ := hq.rsi.symm
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
  have so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block H.initPrologue)
      fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s' :=
    rel_taint args (fun s s' e e' r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hc.pro
      (fun _ e => by rw [e]; exact pro_ok hH hp)
      (fun _ e => by rw [e, ← ei]; exact pro_ok hH hp')
  have c₁ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .rbx) (by simp) si si'
    (fun k => k.rbx) (fun k => k.rbx)
  have c₂ := callInit_rel hH hp hp' hq hc (b := inn s₀) (st := .r12) (by simp) so so'
    (fun k => k.r12) (fun k => by rw [k.r12, eo])
  have keys : RelCT isa (fun s s' => KR H s₀ (inn s₀) s ∧ KR H s₀' (inn s₀) s') H.initKeys
      fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
        (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀)) :=
    rel_taint kregs (fun _ _ h h' => kr_agree hq h h') hc.keys
      (fun _ h => WP.mono (keys_ok hH hp h) fun _ h => ⟨h.1, h.2.1⟩)
      (fun _ h => WP.mono (keys_ok hH hp' (ei ▸ h)) fun _ h => ⟨ei ▸ h.1, by rw [h.2.1, ei]⟩)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => ∃ b, KR H s₀ b s ∧ KR H s₀' b s') (.block H.stream.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs kregs)
      (fun _ _ ⟨_, h, h'⟩ => Taint.agree_ofRegs (kr_agree hq h h')) hr
  exact pro.seq (c₁.seq (c₂.seq (keys.seq ((hbo.rel hp hp' hq).seq restore))))

end

/-- `compBoth` as the compression function on the inner state's block and
then on the outer's (`compTwice`). -/
theorem BothOk.twice (hc : Checks H)
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compTwice H.P.N H.compN H.compC) : BothOk H hH where
  ok {sc s₀} hp {t} hk hsi {Q} k := by
    have si := stOk_in (H := H) hp
    have so := stOk_out (H := H) hp
    have hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
      Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
    have hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
      Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
    have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
    rw [h]
    refine WP.seq (cmp_ok hH hp si hk hsi fun s₅ k₅ f₅ e₅ => ?_)
    refine WP.seq (WP.mono (mid_ok hH hp k₅) fun s₆ ⟨k₆, si₆, m₆⟩ => ?_)
    refine cmp_ok hH hp so k₆ si₆ fun s₇ k₇ f₇ e₇ => k s₇ _ k₇ ?_ ?_
    · rw [stateAt_keep hH hp f₇ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.sub_right hvO).sub_left hvI
          · exact (hp.i_s.sub_right (cal_sub hH hp)).sub_left hvI
          · exact hp.stk_i.symm.sub_left hvI), m₆, e₅]
    · rw [e₇, m₆, stateAt_keep hH hp f₅ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.symm.sub_left hvO).sub_right hvI
          · exact (so.sc.sub_left hvO).sub_right (cal_sub hH hp)
          · exact so.stk.symm.sub_left hvO),
        blockAt_keep hH hp f₅ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro r (rfl | rfl | rfl)
          · exact (hp.i_o.symm.sub_left bO).sub_right hvI
          · exact (so.sc.sub_left bO).sub_right (cal_sub hH hp)
          · exact so.stk.symm.sub_left bO)]
  rel {sc s₀ s₀'} hp hp' hq := by
    have ei : inn s₀' = inn s₀ := hq.rdi.symm
    have eo : out s₀' = out s₀ := hq.rsi.symm
    have si := stOk_in (H := H) hp
    have so := stOk_out (H := H) hp
    have si' : StOk (H := H) (sc := sc) (s₀ := s₀') (inn s₀) := ei ▸ stOk_in (H := H) hp'
    have so' : StOk (H := H) (sc := sc) (s₀ := s₀') (out s₀) := eo ▸ stOk_out (H := H) hp'
    rw [h]
    exact ((cmp_rel hH hp hp' hq si si').seq ((mid_rel hH hp hp' hq hc).seq
      (cmp_rel hH hp hp' hq so so'))).mono (fun _ _ h => h) fun _ _ h => ⟨_, h⟩

/-! ## Both compressions at once -/

/-- `s` is `t` with the arguments of such a function set up. -/
structure PairArgs (N : Nat) (t s : State) : Prop where
  rdi : s.gpr .rdi = t.gpr .rbx
  rdx : s.gpr .rdx = t.gpr .r12
  rcx : s.gpr .rcx = t.gpr .r12 + BitVec.ofNat 64 N
  r8 : s.gpr .r8 = t.gpr .r15
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s.gpr r = t.gpr r
  mem : s.mem = t.mem
  rd : s.rd = t.rd
  wr : s.wr = t.wr

omit hH in
theorem pairArgs_ok (N : Nat) (hN : N < 2 ^ 31) (s : State) :
    WP isa (.block (pairArgs N)) s (PairArgs N s) := by
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ =>
    wp_mov fun s₅ u₅ _ _ => WP.block_nil ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), sx_ofNat hN]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.other r h4, u₄.other r h3, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

section
variable {sc : Nat} {s₀ : State} (hp : Pre H sc s₀)
include hH hp

/-- The precondition of a function that compresses both blocks at once, in
the state `s₁` with its arguments, set up from `t`. -/
theorem pair_pre {t s₁ : State} (hk : KR H s₀ (inn s₀) t) (hsi : t.gpr .rsi = bufOf H (inn s₀))
    (ha : PairArgs H.P.N t s₁) :
    (MdStream.X86_64.compress2K hH.md).pre (s₁.callEntry.withRegions
      [⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀]) ∧
    Covers ([⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] ++ [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀])
      (s₁.rd ++ s₁.wr) ∧
    Covers [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀] s₁.wr := by
  obtain ⟨e1, e2, e3, e4, eo, -, erd, ewr⟩ := ha
  obtain ⟨_, s₆, _, k₆, si₆, m₆⟩ := mid_ok hH hp hk
  have c₀ := callOk hH hp (stOk_in (H := H) hp) hk hsi
  have c₁ := callOk hH hp (stOk_out (H := H) hp) k₆ si₆
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  simp only [MdStream.X86_64.compress2K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp),
    e1, e2, e3, e4, eo .rsi (by decide) (by decide) (by decide) (by decide),
    eo .rsp (by decide) (by decide) (by decide) (by decide), hk.rbx, hk.r12, hk.r15, hsi]
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  have hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have r₁ : s₆.gpr .rsp = t.gpr .rsp := k₆.rsp.trans hk.rsp.symm
  have cv : ∀ {X : List Region}, Covers [⟨bufOf H (inn s₀), H.P.B⟩, ⟨inn s₀, H.P.N⟩, calR H s₀] X →
      Covers [⟨bufOf H (out s₀), H.P.B⟩, ⟨out s₀, H.P.N⟩, calR H s₀] X →
      Covers ([⟨bufOf H (inn s₀), H.P.B⟩, ⟨bufOf H (out s₀), H.P.B⟩] ++
        [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀]) X := by
    intro X h₀ h₁ a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
  have cw : ∀ {X : List Region}, Covers [⟨inn s₀, H.P.N⟩, calR H s₀] X → Covers [⟨out s₀, H.P.N⟩, calR H s₀] X →
      Covers [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀] X := by
    intro X h₀ h₁ a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h₀ a n ⟨_, by simp, hc⟩
    · exact h₁ a n ⟨_, by simp, hc⟩
    · exact h₀ a n ⟨_, by simp, hc⟩
  refine ⟨⟨trivial, trivial, (hp.i_o.sub_left hvI).sub_right hvO, c₀.d₁, c₁.d₁, c₀.d₂,
    (hp.i_o.sub_left bI).sub_right hvO, c₀.d₃, (hp.i_o.symm.sub_left bO).sub_right hvI, c₁.d₂, c₁.d₃, c₀.d₄,
    r₁ ▸ c₁.d₄, c₀.d₅⟩, ?_, ?_⟩
  · rw [erd, ewr]
    exact cv c₀.hc (by rw [hk.rd, hk.wr, ← k₆.rd, ← k₆.wr]; exact c₁.hc)
  · rw [ewr]
    exact cw c₀.hw (by rw [hk.wr, ← k₆.wr]; exact c₁.hw)

/-- The call of a function that compresses both blocks at once. -/
theorem pair_ok {name : String} {code : Prog isa} (hf : MdStream.X86_64.PairOk hH.md code) {t : State}
    (hk : KR H s₀ (inn s₀) t) (hsi : t.gpr .rsi = bufOf H (inn s₀)) {Q : State → Prop}
    (k : ∀ s', KR H s₀ (inn s₀) s' →
      hH.md.stateAt s'.mem (inn s₀) =
        hH.md.compress (hH.md.stateAt t.mem (inn s₀)) (hH.md.blockAt t.mem (bufOf H (inn s₀))) →
      hH.md.stateAt s'.mem (out s₀) =
        hH.md.compress (hH.md.stateAt t.mem (out s₀)) (hH.md.blockAt t.mem (bufOf H (out s₀))) →
      Q s') :
    WP isa (Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) t Q := by
  obtain ⟨-, -, hN, -, hB, -⟩ := sizes hH hp
  have si := stOk_in (H := H) hp
  have so := stOk_out (H := H) hp
  have hvI : Region.Sub ⟨inn s₀, H.P.N⟩ (inR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have hvO : Region.Sub ⟨out s₀, H.P.N⟩ (outR H s₀) :=
    Region.sub_prefix (by show H.P.N ≤ H.P.N + H.P.B; omega_using [])
  have bI : Region.Sub ⟨bufOf H (inn s₀), H.P.B⟩ (inR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have bO : Region.Sub ⟨bufOf H (out s₀), H.P.B⟩ (outR H s₀) := Offset.sub_base _ (Nat.le_refl _)
  have b8 : Region.Sub (below (t.gpr .rsp) 8) (stkR s₀) := by
    rw [hk.rsp]; exact Offset.sub_below _ (by omega_using []) (by omega_using [])
  show WP isa (.seq (.block (pairArgs H.P.N)) (.call name code)) t Q
  refine WP.seq (WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) t) fun s₁ ha => ?_)
  obtain ⟨hpre, hc, hw⟩ := pair_pre hH hp hk hsi ha
  have hsp : s₁.gpr .rsp = t.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide)
  refine WP.call (k := MdStream.X86_64.compress2K hH.md) hf.verified hf.nosp (by rw [hf.depth]; decide)
    hpre hc hw ?_
  intro s₂ hrd hwr hcs hfr _ ⟨s₃, hm₃, _, hpost⟩
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  simp only [MdStream.X86_64.compress2K, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
    hne _ (by decide : Reg.rcx ≠ .rsp), ha.rdi, ha.rdx, ha.rcx,
    ha.other .rsi (by decide) (by decide) (by decide) (by decide), hk.rbx, hk.r12, hsi, hm₃] at hpost
  have f : Frame [⟨inn s₀, H.P.N⟩, ⟨out s₀, H.P.N⟩, calR H s₀, stkR s₀] t.mem s₂.mem := by
    rw [hf.depth, hsp, ha.mem] at hfr
    exact hfr.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨out s₀, H.P.N⟩, by simp, fun _ h => h⟩
      · exact ⟨calR H s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, b8⟩
  have fe : Frame [below (t.gpr .rsp) 8] t.mem s₁.callEntry.mem := by
    rw [← hsp, ← ha.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega_using []) (by omega_using []))
  have one : ∀ {X : Region}, (below (t.gpr .rsp) 8).Disjoint X → ∀ r ∈ [below (t.gpr .rsp) 8], X.Disjoint r :=
    fun h r hr => by rw [List.mem_singleton.mp hr]; exact h.symm
  rw [stateAt_keep hH hp fe (one ((si.stk.sub_left b8).sub_right hvI)),
    blockAt_keep hH hp fe (one ((si.stk.sub_left b8).sub_right bI)),
    stateAt_keep hH hp fe (one ((so.stk.sub_left b8).sub_right hvO)),
    blockAt_keep hH hp fe (one ((so.stk.sub_left b8).sub_right bO))] at hpost
  refine k s₂ (hk.keep (hrd.trans ha.rd) (hwr.trans ha.wr) (fun r hr => ?_) f ?_) hpost.1 hpost.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hcs _ (by simp [calleeSaved])).trans (ha.other _ (by decide) (by decide) (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact away_st hH hp si hvI
    · exact away_st hH hp so hvO
    · exact away_cal hH hp
    · exact away_stk hH hp (fun _ h => h)

end

/-- `compBoth` as one call of a function that compresses both blocks at once
(`compPair`). -/
theorem BothOk.pair {name : String} {code : Prog isa} (hf : MdStream.X86_64.PairOk hH.md code)
    (hta : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block (pairArgs H.P.N)) hc).isSome = true)
    (h : H.compBoth = Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) : BothOk H hH where
  ok {sc s₀} hp {t} hk hsi {Q} k := by
    rw [h]; exact pair_ok hH hp hf hk hsi fun s' k' e₁ e₂ => k s' _ k' e₁ e₂
  rel {sc s₀ s₀'} hp hp' hq := by
    have ei : inn s₀' = inn s₀ := hq.rdi.symm
    have eo : out s₀' = out s₀ := hq.rsi.symm
    obtain ⟨-, -, hN, -⟩ := sizes hH hp
    rw [h]
    have args : RelCT isa (fun s s' => (KR H s₀ (inn s₀) s ∧ s.gpr .rsi = bufOf H (inn s₀)) ∧
          (KR H s₀' (inn s₀) s' ∧ s'.gpr .rsi = bufOf H (inn s₀))) (.block (pairArgs H.P.N))
        fun s s' => (∃ t, (KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s) ∧
          (∃ t, (KR H s₀' (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s') :=
      rel_taint kregs (fun _ _ h h' => kr_agree hq h.1 h'.1) hta
        (fun s h => WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) s) fun _ a => ⟨s, h, a⟩)
        (fun s h => WP.mono (pairArgs_ok H.P.N (by omega_using [hN]) s) fun _ a => ⟨s, h, a⟩)
    have call := VG.X86_64.RelCT.callEx (n := name) (k := MdStream.X86_64.compress2K hH.md)
      (P := fun s s' => (∃ t, (KR H s₀ (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s) ∧
        (∃ t, (KR H s₀' (inn s₀) t ∧ t.gpr .rsi = bufOf H (inn s₀)) ∧ PairArgs H.P.N t s'))
      hf.verified hf.ct fun s₁ s₂ ⟨⟨t, ⟨k, si⟩, a⟩, ⟨t', ⟨k', si'⟩, a'⟩⟩ => by
        obtain ⟨p₁, c₁, w₁⟩ := pair_pre hH hp k si a
        obtain ⟨p₂, c₂, w₂⟩ := pair_pre hH hp' (ei ▸ k') (by rw [si', ei]) a'
        refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, ?_⟩
        · simp only [MdStream.X86_64.compress2K, State.withRegions_gpr,
            State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp)]
          exact ⟨by rw [a.rdi, a'.rdi, k.rbx, k'.rbx],
            by rw [a.other .rsi (by decide) (by decide) (by decide) (by decide),
              a'.other .rsi (by decide) (by decide) (by decide) (by decide), si, si'],
            by rw [a.rdx, a'.rdx, k.r12, k'.r12, eo], by rw [a.rcx, a'.rcx, k.r12, k'.r12, eo],
            by rw [a.r8, a'.r8, k.r15, k'.r15, scr, scr, hq.r8]⟩
        · rw [a.other .rsp (by decide) (by decide) (by decide) (by decide),
            a'.other .rsp (by decide) (by decide) (by decide) (by decide), k.rsp, k'.rsp, hq.rsp]
    exact (rel_wp (c := Impl.Pbkdf2.Md.X86_64.compPair H.P.N name code) (args.seq call)
      (fun s ⟨k, si⟩ => pair_ok hH hp hf k si fun s' k' _ _ => k')
      (fun s ⟨k, si⟩ => pair_ok hH hp' hf (ei ▸ k) (by rw [si, ei]) fun s' k' _ _ => ei ▸ k')).mono
        (fun _ _ h => h) fun _ _ h => ⟨_, h⟩

/-- What `init` needs of `H.compBoth`, whichever of the two it is. -/
theorem bothOk (hc : Checks H) : BothOk H hH := by
  rcases hH.both with h | ⟨name, code, h, hf, hta⟩
  · exact .twice hH hc h
  · exact .pair hH hf hta h

/-- HMAC's `init` is verified against `initG`, given the taint checks and the
facts about its code that the kernel checks for each hash function. -/
theorem verified {sc : Nat} (hbo : BothOk H hH) (hc : Checks H) (hfit : H.stream.buf ≤ 8 * sc)
    (hmx : H.hmacInit.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.hmacInit (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct hH (pre_of hH hs hfit) hbo
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpub
    exact (ct hH (pre_of hH h₁ hfit) (pre_of hH h₂ hfit) ⟨h1, h2, h3, h4, h5, h6⟩ hbo hc
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Pbkdf2.Md.X86_64.HmacInit
