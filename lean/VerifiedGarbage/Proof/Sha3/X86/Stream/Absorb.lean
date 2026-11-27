module

public import VerifiedGarbage.Proof.Sha3.X86.Permute
public import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Sha3.X86.Lit
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.X86.Permute
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.Sha3.X86.Lit
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Sha512.X86.Compress
meta import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-!
# The SHA-3 sponge on x86 (32-bit): eight bytes at a time

What `absorb` and `squeeze` share for their turns of eight bytes: the two
`movq` that copy eight bytes and the four instructions that XOR eight bytes
into eight others, each run once for any registers and addresses; a 64-bit
word of memory as its bytes; and the position in the block after bytes that
fit in it.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Stream

open VG VG.X86
open VG.Proof.Sha256.X86.Stream (Mupd WP.cons)
open VG.Proof.Sha512.X86 (mem_rd qword_append_0 q_pxor)
open VG.Spec.Sha3 (stateAt bytesAt)

theorem exec_movqLoad (d : XReg) (m : MemOp) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.ea m) 8) :
    exec (.movqLoad d m) s = some (s.setXmm d ((0 : BitVec 64) ++ s.mem.readW (s.ea m) 64)) := by
  show (s.load64 (s.ea m)).map _ = _
  rw [State.load64, ite_eq_left hin]
  rfl

theorem exec_movqStore (m : MemOp) (r : XReg) (s : State) (hout : InRegions s.wr (s.ea m) 8) :
    exec (.movqStore m r) s = some { s with mem := s.mem.writeW (s.ea m) (qword (s.xmm r) 0) } := by
  show s.store64 (s.ea m) ((s.xmm r).extractLsb' 0 64) = _
  rw [State.store64, ite_eq_left hout]
  rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movq x, [a]; movq [b], x`: eight bytes copied. -/
theorem wp_copy8 {ma mb : MemOp} {a b : Addr} {x : XReg} (ha : s.ea ma = a) (hb : s.ea mb = b)
    (hin : InRegions (s.rd ++ s.wr) a 8) (hout : InRegions s.wr b 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW b (s.mem.readW a 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.movqLoad x ma :: .movqStore mb x :: is)) s Q := by
  subst ha hb
  refine WP.cons (exec_movqLoad x ma s hin) (WP.cons (exec_movqStore mb x _ hout) (k _ ⟨rfl, ?_, rfl, rfl⟩))
  show s.mem.writeW (s.ea mb) (qword ((s.setXmm x ((0 : BitVec 64) ++ s.mem.readW (s.ea ma) 64)).xmm x) 0) = _
  rw [VG.X86.RegUpd.xmm_setXmm_self, qword_append_0]

/-- What `movq x, a; movq y, b; pxor x, y` leaves in `x`. -/
theorem xor8_val (s : State) {x y : XReg} (hxy : x ≠ y) (A B : BitVec 128) :
    qword ((((s.setXmm x A).setXmm y B).setXmm x (XBinOp.eval .pxor (((s.setXmm x A).setXmm y B).xmm x)
      (((s.setXmm x A).setXmm y B).xmm y))).xmm x) 0 = qword A 0 ^^^ qword B 0 := by
  rw [VG.X86.RegUpd.xmm_setXmm_self, q_pxor, VG.X86.RegUpd.xmm_setXmm_of_ne _ _ hxy,
    VG.X86.RegUpd.xmm_setXmm_self, VG.X86.RegUpd.xmm_setXmm_self]

/-- `movq x, [a]; movq y, [b]; pxor x, y; movq [b], x`: the eight bytes at
`a` XORed into those at `b`. -/
theorem wp_xor8 {ma mb : MemOp} {a b : Addr} {x y : XReg} (hxy : x ≠ y) (ha : s.ea ma = a) (hb : s.ea mb = b)
    (hin : InRegions (s.rd ++ s.wr) a 8) (hout : InRegions s.wr b 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW b (s.mem.readW a 64 ^^^ s.mem.readW b 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.movqLoad x ma :: .movqLoad y mb :: .xop (.bin .pxor x y) :: .movqStore mb x :: is)) s Q := by
  subst ha hb
  refine WP.cons (exec_movqLoad x ma s hin) (WP.cons (exec_movqLoad y mb _ (mem_rd hout))
    (WP.cons (s' := XOp.exec (.bin .pxor x y) _) rfl (WP.cons (exec_movqStore mb x _ hout)
      (k _ ⟨rfl, ?_, rfl, rfl⟩))))
  refine (congrArg (s.mem.writeW (s.ea mb)) (xor8_val s hxy _ _)).trans ?_
  rw [qword_append_0, qword_append_0]
  rfl

end

theorem ofNat_add_ofNat (x : BitVec 32) (k n : Nat) :
    x + BitVec.ofNat 32 k + BitVec.ofNat 32 n = x + BitVec.ofNat 32 (k + n) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A byte of a 64-bit word read at `a`. -/
theorem readW64_byte (m : Mem) (a : Addr) {d : Nat} (hd : d < 8) :
    (m.readW a 64).extractLsb' (8 * d) 8 = m (a + BitVec.ofNat 64 d) := by
  rw [Mem.readW, BitVec.setWidth_eq, Mem.extractLsb'_read m a (n := 64 / 8) (show d < 64 / 8 from hd)]

/-- A byte before or after a 64-bit word written at `p + i`. -/
theorem writeW64_other (m : Mem) (p : Addr) (v : BitVec 64) {i j : Nat} (hi : i + 8 ≤ 2 ^ 32)
    (hj : j < 2 ^ 32) (h : j < i ∨ i + 8 ≤ j) :
    (m.writeW (p + BitVec.ofNat 64 i) v) (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) :=
  Mem.write_apply (by
    show ¬ (p + BitVec.ofNat 64 j - (p + BitVec.ofNat 64 i)).toNat < 8
    bv_omega)

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, Proof.Sha3.bytesAt_succ, bytesAt_add m p c n, Proof.Sha3.bytesAt_succ,
      List.append_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Eight bytes of a state in memory written: XORed with `bs`. -/
theorem stateAt_write_word {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = Proof.Sha3.xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [Proof.Sha3.byteOf_xorAt _ _ _ hi, Proof.Sha3.byteOf_stateAt _ _ hi, Proof.Sha3.byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        Proof.Sha3.writeW64_byte _ _ _ (by omega_arith), hv _ (by omega_arith), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, writeW64_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]

/-- The position in the block after `n` more bytes that fit in it. -/
theorem pos_add {r p c n : Nat} (hr : 0 < r) (hfit : (p + c) % r + n ≤ r) :
    (p + (c + n)) % r = if (p + c) % r + n = r then 0 else (p + c) % r + n := by
  obtain e := Nat.div_add_mod (p + c) r
  obtain hj := Nat.mod_lt (p + c) hr
  rw [show p + (c + n) = (p + c) + n by omega_using []]
  generalize (p + c) % r = j at e hj hfit ⊢
  generalize (p + c) / r = q at e
  rw [← e]
  split
  · rw [Nat.add_assoc, ‹j + n = r›, ← Nat.mul_succ, Nat.mul_mod_right]
  · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]

end VG.Proof.Sha3.X86.Stream

end

/-! ### `Sha3.X86.Stream.Squeeze`, which the modules that import this one used -/

section

/-!
# The SHA-3 sponge on x86 (32-bit): `squeeze`

The structure of the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Squeeze`),
with `state` in `ebx`, `scratch` in `ebp`, `out` in `esi`, the bytes left in
`edi`, and `state + pos` and `rate` in the scratch space. A turn of the loop
copies eight bytes (`word_ok`) where the block and the output have eight
left, and one byte (`store_ok`) otherwise (`turn_ok`): the invariant is the
same after either, eight bytes or one further on.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Stream.Squeeze

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add
  wp_addi wp_sub wp_subi wp_cmp wp_cmpi wp_test contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32)
open VG.Proof.Sha3 (byteOf byteOf_stateAt iterF iterF_succ length_squeezeFrom squeezeFrom_getElem
  squeezeFrom_iterF writeW8_self writeW8_other rate_bounds contains_offset div_mod_eq)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos₀ : Nat := (arg s₀ 2).toNat
abbrev op : BitVec 32 := arg s₀ 3
abbrev outn : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev oA : Addr := (op s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev oR : Region := ⟨oA s₀, outn s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12
/-- The initial state. -/
abbrev S₀ : Spec.Sha3.State := stateAt s₀.mem (stA s₀)

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (addr (scr s₀)) s₀.gpr saved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, oR s₀, scR s₀, argR s₀]
  st_o : (stR s₀).Disjoint (oR s₀)
  st_scr : (stR s₀).Disjoint (scR s₀)
  o_scr : (oR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_o : (argR s₀).Disjoint (oR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_o : (retR s₀).Disjoint (oR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_o : (stkR s₀).Disjoint (oR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  o_fit : (op s₀).toNat + outn s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_le : pos₀ s₀ ≤ rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.squeezeX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  obtain e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19, h20, h21⟩

theorem outn_lt (s₀ : State) : outn s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 24⟩ := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have := rate_bounds hp.rate; omega_arith

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega_arith) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [scR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 28) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  obtain fit : (E s₀).toNat + 4 + 24 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_arith
  obtain hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega_arith) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the scratch space. -/
theorem frame_scr {rs : List Region} (hr : scR s₀ ∈ rs) {m : Mem} {m₀ : Mem} (hf : Frame rs m₀ m) {d : Nat}
    (hd : d + 4 ≤ 640) (v : BitVec 32) : Frame rs m₀ (m.writeW (addr (scr s₀) d) v) :=
  hf.writeW hr _ (contains_addr hd (by omega_arith) hp.scr_fit)

/-- The words of the scratch space beyond what the permutation uses. -/
theorem hi_sep {d : Nat} (hd₁ : 512 ≤ d) (hd : d + 4 ≤ 640) :
    ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  obtain hs := sub_word (N := 640) hp.scr_fit hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hs
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega_arith)] at h₁
    obtain hE := addr_toNat (scr s₀)
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
  · exact hp.stk_scr.symm.sub_left hs

/-- A word of the scratch space is unchanged by a write to `out`. -/
theorem scr_o (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < outn s₀) (v : Byte) :
    (m.writeW (oA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.o_scr.symm.sep (contains_addr hd (by omega_arith) hp.scr_fit)
    (contains_offset (by omega_arith) (by have := outn_lt s₀; omega_arith))) (by decide)

end Pre

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by decide

theorem saved_fits : Spill.Fits 528 saved := by decide

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 528 → m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32) :
    Saved s₀ m' :=
  hs.of_readW fun p hp' => hk _ (saved_bound p hp').1 (saved_bound p hp').2

/-! ## The loop invariant -/

/-- After `i` bytes of output, `k` permutations and `pos` bytes of the
current block: `pos₀ + i = rate * k + pos`. -/
structure Inv (s₀ : State) (i k pos : Nat) (s : State) : Prop where
  i_le : i ≤ outn s₀
  hi : pos₀ s₀ + i = rt s₀ * k + pos
  pos_le : pos ≤ rt s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = E s₀
  esi : s.gpr .esi = op s₀ + BitVec.ofNat 32 i
  edi : s.gpr .edi = BitVec.ofNat 32 (outn s₀ - i)
  ptr : s.mem.readW (addr (scr s₀) 528) 32 = st s₀ + BitVec.ofNat 32 pos
  rate : s.mem.readW (addr (scr s₀) 532) 32 = arg s₀ 1
  frame : Frame [stR s₀, oR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  state : stateAt s.mem (stA s₀) = iterF k (S₀ s₀)
  out : ∀ j < i, s.mem (oA s₀ + BitVec.ofNat 64 j) =
    byteOf (iterF ((pos₀ s₀ + j) / rt s₀) (S₀ s₀)) ((pos₀ s₀ + j) % rt s₀)

theorem Inv.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Inv s₀ i k pos s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ i k pos s' where
  i_le := h.i_le
  hi := h.hi
  pos_le := h.pos_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  esi := by rw [hg _ (by simp)]; exact h.esi
  edi := by rw [hg _ (by simp)]; exact h.edi
  ptr := by rw [hm]; exact h.ptr
  rate := by rw [hm]; exact h.rate
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  state := by rw [hm]; exact h.state
  out := by rw [hm]; exact h.out

/-! ## The prologue -/

theorem setup_eq : setup = .mov .eax (.mem (at_ .esp 24)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 12)),
    .alu .add .ecx (.reg .ebx), .store (at_ .ebp 528) .ecx, .mov .ecx (.mem (at_ .esp 8)),
    .store (at_ .ebp 532) .ecx, .mov .esi (.mem (at_ .esp 16)), .mov .edi (.mem (at_ .esp 20)),
    .alu .test .edi (.reg .edi)] : List Instr)) := rfl

/-- The memory after saving the registers. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr saved

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 0 (pos₀ s₀) s ∧ s.zf = some (decide (outn s₀ = 0)) := by
  have fC := hp.scr_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hp.pos_le
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [setup_eq]
  refine wp_movm (a := addr (E s₀) 24) (ea_at _ _ _) (hp.arg_in rfl (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e1]; exact hp.scr_out u₁.wr (by have := saved_bound p h; omega_arith)) fun s₅ u₅ => ?_
  obtain g₅ : ∀ r, r ≠ .eax → s₅.gpr r = s₀.gpr r := fun r h => by rw [u₅.gpr, u₁.other r h]
  obtain m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, e1, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  obtain r₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  obtain hsc : scR s₀ ∈ [scR s₀] := List.mem_singleton_self _
  obtain f₅ : Frame [scR s₀] s₀.mem s₅.mem := by
    rw [m₅]
    exact Spill.saveMem_frame hsc _ _ _ _ fun p h =>
      contains_addr (by have := saved_bound p h; omega_arith) (by omega_arith) fC
  obtain sv₅ : Saved s₀ s₅.mem := by
    rw [m₅]; exact Spill.saveMem_saved_addr _ _ saved_fits (by omega_arith)
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_movm (a := addr (E s₀) 4) (by rw [ea_at, u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₆.wr, w₅]) (by omega_arith) (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (E s₀) 12) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in (by rw [u₇.wr, u₆.wr, w₅]) (by omega_arith) (by omega_arith)) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  obtain e5 : s₅.gpr .eax = scr s₀ := by rw [u₅.gpr, e1]
  obtain hb₉ : s₉.gpr .ebp = scr s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e5]
  obtain m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  obtain hst : s₇.gpr .ebx = st s₀ := by
    rw [u₇.gpr, u₆.mem, hp.arg_keep f₅ (by omega_arith) (by omega_arith)]; rfl
  obtain hpos : s₉.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos₀ s₀) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), hst, u₇.mem, u₆.mem, hp.arg_keep f₅ (by omega_arith) (by omega_arith),
      BitVec.add_comm]
    show _ = _ + BitVec.ofNat 32 (arg s₀ 2).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₉])
    (hp.scr_out (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_arith)) fun s₁₀ u₁₀ => ?_
  obtain f₁₀ : Frame [scR s₀] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem, m₈]; exact hp.frame_scr hsc f₅ (by omega_arith) _
  refine wp_movm (a := addr (E s₀) 8) (by rw [ea_at, u₁₀.gpr, u₉.other _ (by decide),
    u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_arith) (by omega_arith)) fun s₁₁ u₁₁ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₁₁.other _ (by decide), u₁₀.gpr, hb₉])
    (hp.scr_out (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_arith)) fun s₁₂ u₁₂ => ?_
  obtain f₁₂ : Frame [scR s₀] s₀.mem s₁₂.mem := by
    rw [u₁₂.mem, u₁₁.mem]; exact hp.frame_scr hsc f₁₀ (by omega_arith) _
  obtain hw₁₂ : s₁₂.wr = s₀.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  refine wp_movm (a := addr (E s₀) 16) (by rw [ea_at, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr,
    u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in hw₁₂ (by omega_arith) (by omega_arith)) fun s₁₃ u₁₃ => ?_
  refine wp_movm (a := addr (E s₀) 20) (by rw [ea_at, u₁₃.other _ (by decide), u₁₂.gpr,
    u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
    u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₃.wr, hw₁₂]) (by omega_arith) (by omega_arith)) fun s₁₄ u₁₄ => ?_
  refine wp_test fun s₁₅ u₁₅ z₁₅ => WP.block_nil ?_
  -- The registers and memory at the end.
  obtain g : ∀ r, r ∉ [Reg.eax, .ebp, .ebx, .ecx, .esi, .edi] → s₁₅.gpr r = s₀.gpr r := fun r hr => by
    have ⟨a, b, c', d, e, f⟩ : r ≠ .eax ∧ r ≠ .ebp ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .esi ∧ r ≠ .edi := by
      simpa using hr
    rw [u₁₅.gpr, u₁₄.other r f, u₁₃.other r e, u₁₂.gpr, u₁₁.other r d, u₁₀.gpr, u₉.other r d,
      u₈.other r d, u₇.other r c', u₆.other r b, g₅ r a]
  obtain hm : s₁₅.mem = s₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  obtain hm₁₂ : s₁₂.mem = (s₁₀.mem.writeW (addr (scr s₀) 532) (s₁₁.gpr .ecx)) := by
    rw [u₁₂.mem, u₁₁.mem]
  obtain hrate : s₁₁.gpr .ecx = arg s₀ 1 := by
    rw [u₁₁.gpr, hp.arg_keep f₁₀ (by omega_arith) (by omega_arith)]; rfl
  obtain hdi : s₁₄.gpr .edi = arg s₀ 4 := by
    rw [u₁₄.gpr, u₁₃.mem, hp.arg_keep f₁₂ (by omega_arith) (by omega_arith)]; rfl
  refine ⟨⟨Nat.zero_le _, by simp, hpl, ?_, by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, hw₁₂], ?_, ?_, g .esp (by decide),
    ?_, ?_, ?_, ?_, by rw [hm]; exact f₁₂.mono (by simp), ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩,
    ?_⟩
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, r₅]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hst]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, hb₉]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, hp.arg_keep f₁₂ (by omega_arith) (by omega_arith), BitVec.add_zero]
    rfl
  · rw [u₁₅.gpr, hdi, Nat.sub_zero]; simp [outn]
  · rw [hm, hm₁₂, sep _ _ 528 532 (by omega_arith) (by omega_arith) (by omega_arith), u₁₀.mem, Mem.readW_writeW_self32]
    exact hpos
  · rw [hm, hm₁₂, Mem.readW_writeW_self32, hrate]
  · rw [hm, hm₁₂]
    refine sv₅.keep fun d h1 h2 => ?_
    rw [sep _ _ d 532 (by omega_arith) (by omega_arith) (by omega_arith), u₁₀.mem, u₉.mem, m₈,
      sep _ _ d 528 (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [hm]
    exact Proof.Sha3.stateAt_congr fun i hi => f₁₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · rw [z₁₅, hdi, BitVec.and_self]
    rw [show arg s₀ 4 = BitVec.ofNat 32 (outn s₀) by simp [outn],
      VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (outn_lt s₀)]

/-! ## One iteration -/

theorem check_eq : loadVars ++ atEnd = [.mov .ecx (.mem (at_ .ebp 528)), .mov .edx (.mem (at_ .ebp 532)),
    .mov .eax (.reg .ecx), .alu .sub .eax (.reg .ebx), .alu .cmp .eax (.reg .edx)] := rfl

/-- Test whether the block is used up. -/
theorem check_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s) :
    WP isa (.block (loadVars ++ atEnd)) s fun s' =>
      Inv s₀ i k pos s' ∧ s'.zf = some (decide (pos = rt s₀)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hI.pos_le
  rw [check_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega_arith))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp])
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_sub fun s₄ u₄ _ => wp_cmp fun s₅ u₅ _ z₅ => WP.block_nil ?_
  obtain g : ∀ r, r ∉ [Reg.ecx, .edx, .eax] → s₅.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b, c⟩ : r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .eax := by simpa using hr
    rw [u₅.gpr, u₄.other r c, u₃.other r c, u₂.other r b, u₁.other r a]
  refine ⟨hI.congr (fun r hr => g r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]), ?_⟩
  obtain hax : s₄.gpr .eax = BitVec.ofNat 32 pos := by
    rw [u₄.gpr, u₃.gpr, u₃.other .ebx (by decide), u₂.other .ecx (by decide), u₂.other .ebx (by decide),
      u₁.gpr, u₁.other .ebx (by decide), hI.ptr, hI.ebx, add_sub_self]
  obtain hdx : s₄.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hI.rate]
    simp [rt]
  rw [z₅, hax, hdx, VG.Proof.Sha256.X86.Stream.sub_beq (by omega_arith) (by omega_arith)]

theorem permute_ok {s₀ : State} (hp : Pre s₀) {i k : Nat} {s : State} (hI : Inv s₀ i k (rt s₀) s) :
    WP isa (.seq (.block [.store (at_ .ebp pOff) .ebx]) (permuteCall .ebx .ebp)) s (Inv s₀ i (k + 1) 0) := by
  have fC := hp.scr_fit
  refine WP.seq (wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]; rfl)
    (hp.scr_out hI.wr (by omega_arith)) fun s₁ u₁ => WP.block_nil ?_)
  obtain hwr : s₁.wr = s₀.wr := u₁.wr.trans hI.wr
  obtain e₁ : ∀ r, s₁.gpr r = s.gpr r := fun r => by rw [u₁.gpr]
  refine permuteCall_ok (st := .ebx) (scr := .ebp) (by decide) (by decide) (by rw [e₁, hI.esp])
    (by rw [e₁, hI.ebx]) (by rw [e₁, hI.ebp]) hp.sp_lo hp.st_fit (by omega_arith)
    (hp.st_scr.sub_right (Region.sub_prefix (by omega_arith))) hp.stk_st
    (hp.stk_scr.sub_right (Region.sub_prefix (by omega_arith))) (by rw [hwr, hp.wr]; simp)
    (by rw [hwr, hp.wr]; simp) fun s' rd' wr' cs' hf hst => ?_
  obtain hd : ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], (oR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_o.symm
    · exact hp.o_scr.sub_right (Region.sub_prefix (by omega_arith))
    · exact hp.stk_o.symm
  obtain hfw : Frame [scR s₀] s.mem s₁.mem := by
    rw [u₁.mem]; exact hp.frame_scr (List.mem_singleton_self _) (Frame.refl _ _) (by omega_arith) _
  obtain keep : ∀ d, 512 ≤ d → d + 4 ≤ 640 →
      s'.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 =>
    hf.readW (Region.contains_self _ _) (hp.hi_sep h1 h2) (by decide)
  refine ⟨hI.i_le, by rw [hI.hi, Nat.mul_succ]; rfl, Nat.zero_le _, rd'.trans (u₁.rd.trans hI.rd),
    wr'.trans hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cs' _ (by decide), e₁, hI.ebx]
  · rw [cs' _ (by decide), e₁, hI.ebp]
  · rw [cs' _ (by decide), e₁, hI.esp]
  · rw [cs' _ (by decide), e₁, hI.esi]
  · rw [cs' _ (by decide), e₁, hI.edi]
  · rw [keep 528 (by omega_arith) (by omega_arith), u₁.mem, Mem.readW_writeW_self32, hI.ebx]; simp
  · rw [keep 532 (by omega_arith) (by omega_arith), u₁.mem, word_sep (N := 640) fC (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hI.rate
  · refine hI.frame.trans ((hfw.mono (by simp)).trans (hf.sub fun r hr => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  · refine hI.saved.keep fun d h1 h2 => ?_
    rw [keep d h1 (by omega_arith), u₁.mem, word_sep (N := 640) fC (by omega_arith) (by omega_arith) (by omega_arith)]
  · rw [hst, show stateAt s₁.mem (stA s₀) = stateAt s.mem (stA s₀) from
      Proof.Sha3.stateAt_congr fun i hi => hfw.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi,
      hI.state, iterF_succ]
  · intro j hj
    obtain hj' : j < outn s₀ := by have := hI.i_le; omega_arith
    rw [hf.bytes (R := oR s₀) hd (by have := outn_lt s₀; show outn s₀ ≤ 2 ^ 64; omega_arith) hj',
      hfw.bytes (R := oR s₀) (by simpa using hp.o_scr) (by have := outn_lt s₀; show outn s₀ ≤ 2 ^ 64; omega_arith) hj']
    exact hI.out j hj

/-- After `loadVars`: the invariant, with `state + pos` in `ecx` and `rate`
in `edx`. -/
structure Ready (s₀ : State) (i k pos : Nat) (s : State) : Prop extends Inv s₀ i k pos s where
  ecx : s.gpr .ecx = st s₀ + BitVec.ofNat 32 pos
  edx : s.gpr .edx = arg s₀ 1

theorem load_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s) :
    WP isa (.block loadVars) s (Ready s₀ i k pos) := by
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]; rfl) (hp.scr_in hI.wr (by omega_arith))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp]; rfl)
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega_arith)) fun s₂ u₂ => WP.block_nil ?_
  exact ⟨hI.congr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [u₂.other r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
        u₁.other r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]),
    by rw [u₂.other _ (by decide), u₁.gpr, hI.ptr], by rw [u₂.gpr, u₁.mem]; exact hI.rate⟩

/-- The registers `ecx` and `edx` hold after other instructions that keep them. -/
theorem Ready.congr {s₀ : State} {i k pos : Nat} {s s' : State} (h : Ready s₀ i k pos s)
    (hg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Ready s₀ i k pos s' :=
  ⟨h.toInv.congr (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) hm hrd hwr,
    by rw [hg _ (by decide)]; exact h.ecx, by rw [hg _ (by decide)]; exact h.edx⟩

/-- The test for eight bytes left in the block. -/
theorem room_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hR : Ready s₀ i k pos s) :
    WP isa (.block room8) s fun s' =>
      Ready s₀ i k pos s' ∧ s'.cf = some (decide (rt s₀ < pos + 8)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hR.pos_le
  refine wp_mov fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_addi fun s₃ u₃ => wp_cmp fun s₄ u₄ c₄ _ =>
    WP.block_nil ⟨hR.congr (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr])
      (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]), ?_⟩
  obtain hax : s₃.gpr .eax = BitVec.ofNat 32 (pos + 8) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ebx (by decide), hR.ecx, hR.ebx, add_sub_self]
    exact (BitVec.ofNat_add pos 8).symm
  obtain hdx : s₃.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hR.edx]
    simp [rt]
  rw [c₄, hax, hdx, VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith),
    VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith)]

/-- The test for eight bytes of output left. -/
theorem left_ok {s₀ : State} {i k pos : Nat} {s : State} (hR : Ready s₀ i k pos s) :
    WP isa (.block [.alu .cmp .edi (.imm 8)]) s fun s' =>
      Ready s₀ i k pos s' ∧ s'.cf = some (decide (outn s₀ - i < 8)) := by
  obtain hn := outn_lt s₀
  refine wp_cmpi fun s₁ u₁ c₁ _ => WP.block_nil ⟨hR.congr (fun r _ => by rw [u₁.gpr]) u₁.mem u₁.rd u₁.wr, ?_⟩
  rw [c₁, hR.edi, VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith)]
  rfl

theorem store_eq : squeezeByte ++ storeVars ++ step =
    [.movzx8 .eax (at_ .ecx 0), .store8 (at_ .esi 0) .al, .alu .add .ecx (.imm 1),
      .store (at_ .ebp 528) .ecx, .store (at_ .ebp 532) .edx, .alu .add .esi (.imm 1),
      .alu .sub .edi (.imm 1)] := rfl

/-- A turn of one byte. -/
theorem store_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hR : Ready s₀ i k pos s)
    (hlt : pos < rt s₀) (hi : i < outn s₀) :
    WP isa (.block (squeezeByte ++ storeVars ++ step)) s fun s' =>
      Inv s₀ (i + 1) k (pos + 1) s' ∧ s'.zf = some (decide (outn s₀ - (i + 1) = 0)) := by
  have hI := hR.toInv
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hn := outn_lt s₀
  obtain fC := hp.scr_fit; have fS := hp.st_fit; have fO := hp.o_fit
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [store_eq]
  obtain e₂ := hR.ecx
  obtain d₂ := hR.edx
  obtain hsA : addr (st s₀ + BitVec.ofNat 32 pos) 0 = stA s₀ + BitVec.ofNat 64 pos := ptr_addr (by omega_arith)
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 pos) (by rw [ea_at, e₂, hsA])
    ⟨stR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr],
      contains_offset (by omega_arith) (by omega_arith)⟩ fun s₃ u₃ => ?_
  obtain hoA : addr (op s₀ + BitVec.ofNat 32 i) 0 = oA s₀ + BitVec.ofNat 64 i := ptr_addr (by omega_arith)
  refine wp_store8 (r := .al) (a := oA s₀ + BitVec.ofNat 64 i)
    (by rw [ea_at, u₃.other _ (by decide), hI.esi, hoA])
    (by rw [u₃.wr, hI.wr, hp.wr]; exact ⟨oR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => ?_
  obtain e₅ : s₅.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos + 1) := by
    rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), e₂, ofNat_add_one]
  obtain hb₅ : s₅.gpr .ebp = scr s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), hI.ebp]
  obtain w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₅]) (hp.scr_out w₅ (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₆.gpr, hb₅])
    (hp.scr_out (by rw [u₆.wr, w₅]) (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_addi fun s₈ u₈ => wp_subi fun s₉ u₉ z₉ => WP.block_nil ?_
  -- The memory.
  obtain hb : s.mem (stA s₀ + BitVec.ofNat 64 pos) = byteOf (iterF k (S₀ s₀)) pos := by
    rw [← hI.state, VG.Proof.Sha3.byteOf_stateAt _ _ (by omega_arith)]
  obtain hm₄ : s₄.mem = s.mem.writeW (oA s₀ + BitVec.ofNat 64 i) (byteOf (iterF k (S₀ s₀)) pos) := by
    rw [u₄.mem, show Reg8.al.reg = Reg.eax from rfl, u₃.gpr, u₃.mem, byte_low, hb]
  obtain hm : s₉.mem = (s₄.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (pos + 1))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), d₂,
      u₆.mem, u₅.mem, e₅]
  obtain hfo : Frame [oR s₀] s.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega_arith) (by omega_arith))
  obtain hfc : Frame [scR s₀] s₄.mem s₉.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)
  -- The registers.
  obtain g : ∀ r, r ∉ [Reg.ecx, .edx, .eax, .esi, .edi] → s₉.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b, c', d, e⟩ : r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .eax ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₉.other r e, u₈.other r d, u₇.gpr, u₆.gpr, u₅.other r a, u₄.gpr, u₃.other r c']
  obtain h₉ : s₉.gpr .edi = BitVec.ofNat 32 (outn s₀ - (i + 1)) := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), hI.edi,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, by rw [g _ (by decide), hI.ebx],
    by rw [g _ (by decide), hI.ebp], by rw [g _ (by decide), hI.esp], ?_, h₉, ?_, ?_,
    hI.frame.trans ((hfo.mono (by simp)).trans (hfc.mono (by simp))), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), hI.esi, ofNat_add_one]
  · rw [hm, sep _ _ 528 532 (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
  · rw [hm, Mem.readW_writeW_self32]
  · refine hI.saved.keep fun d h1 h2 => ?_
    rw [hm, sep _ _ d 532 (by omega_arith) (by omega_arith) (by omega_arith), sep _ _ d 528 (by omega_arith) (by omega_arith) (by omega_arith),
      hm₄, hp.scr_o _ (by omega_arith) hi]
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hj,
      Proof.Sha3.stateAt_congr fun j hj => hfo.bytes (R := stR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hfc.bytes (R := oR s₀) (by simpa using hp.o_scr) (by show outn s₀ ≤ 2 ^ 64; omega_arith)
      (show j < outn s₀ by omega_arith), hm₄]
    by_cases e : j = i
    · subst e
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr₀ hlt
      rw [writeW8_self, hI.hi, d, m]
    · rw [writeW8_other _ _ (Offset.add_ofNat_ne _ (by omega_arith) (by omega_arith) e)]
      exact hI.out j (by omega_arith)
  · rw [z₉, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), hI.edi,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega_arith), Nat.sub_sub,
      VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega_arith)]

theorem word_eq : squeezeWord ++ storeVars8 ++ step8 =
    [.movqLoad .xmm0 (at_ .ecx 0), .movqStore (at_ .esi 0) .xmm0, .alu .add .ecx (.imm 8),
      .store (at_ .ebp 528) .ecx, .store (at_ .ebp 532) .edx, .alu .add .esi (.imm 8),
      .alu .sub .edi (.imm 8)] := rfl

/-- A turn of eight bytes. -/
theorem word_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hR : Ready s₀ i k pos s)
    (hlt : pos + 8 ≤ rt s₀) (hi : i + 8 ≤ outn s₀) :
    WP isa (.block (squeezeWord ++ storeVars8 ++ step8)) s fun s' =>
      Inv s₀ (i + 8) k (pos + 8) s' ∧ s'.zf = some (decide (outn s₀ - (i + 8) = 0)) := by
  have hI := hR.toInv
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hn := outn_lt s₀
  obtain fC := hp.scr_fit; have fS := hp.st_fit; have fO := hp.o_fit
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [word_eq]
  obtain hsA : addr (st s₀ + BitVec.ofNat 32 pos) 0 = stA s₀ + BitVec.ofNat 64 pos := ptr_addr (by omega_arith)
  obtain hoA : addr (op s₀ + BitVec.ofNat 32 i) 0 = oA s₀ + BitVec.ofNat 64 i := ptr_addr (by omega_arith)
  refine wp_copy8 (a := stA s₀ + BitVec.ofNat 64 pos) (b := oA s₀ + BitVec.ofNat 64 i)
    (by rw [ea_at, hR.ecx, hsA]) (by rw [ea_at, hI.esi, hoA])
    ⟨stR s₀, by simp [hI.rd, hI.wr, hp.rd, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩
    (by rw [hI.wr, hp.wr]; exact ⟨oR s₀, by simp, contains_offset (by omega_arith) (by omega_arith)⟩)
    fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => ?_
  obtain e₅ : s₅.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos + 8) := by
    rw [u₅.gpr, u₄.gpr, hR.ecx]; exact ofNat_add_ofNat _ _ 8
  obtain hb₅ : s₅.gpr .ebp = scr s₀ := by rw [u₅.other _ (by decide), u₄.gpr, hI.ebp]
  obtain w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₅]) (hp.scr_out w₅ (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₆.gpr, hb₅])
    (hp.scr_out (by rw [u₆.wr, w₅]) (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_addi fun s₈ u₈ => wp_subi fun s₉ u₉ z₉ => WP.block_nil ?_
  -- The memory.
  obtain hm₄ := u₄.mem
  obtain hm : s₉.mem = (s₄.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (pos + 8))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₅.other _ (by decide), u₄.gpr, hR.edx, u₆.mem, u₅.mem, e₅]
  obtain hfo : Frame [oR s₀] s.mem s₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega_arith) (by omega_arith))
  obtain hfc : Frame [scR s₀] s₄.mem s₉.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)
  -- The registers.
  obtain g : ∀ r, r ∉ [Reg.ecx, .esi, .edi] → s₉.gpr r = s.gpr r := fun r hr => by
    have ⟨a, d, e⟩ : r ≠ .ecx ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₉.other r e, u₈.other r d, u₇.gpr, u₆.gpr, u₅.other r a, u₄.gpr]
  obtain h₉ : s₉.gpr .edi = BitVec.ofNat 32 (outn s₀ - (i + 8)) := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, hI.edi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      VG.Proof.Sha256.X86.Stream.sub_ofNat (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, by have := hI.hi; omega_arith, by omega_arith, ?_, ?_, by rw [g _ (by decide), hI.ebx],
    by rw [g _ (by decide), hI.ebp], by rw [g _ (by decide), hI.esp], ?_, h₉, ?_, ?_,
    hI.frame.trans ((hfo.mono (by simp)).trans (hfc.mono (by simp))), ?_, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, hI.esi]
    exact ofNat_add_ofNat _ _ 8
  · rw [hm, sep _ _ 528 532 (by omega_arith) (by omega_arith) (by omega_arith), Mem.readW_writeW_self32]
  · rw [hm, Mem.readW_writeW_self32]
  · refine hI.saved.keep fun d h1 h2 => ?_
    rw [hm, sep _ _ d 532 (by omega_arith) (by omega_arith) (by omega_arith), sep _ _ d 528 (by omega_arith) (by omega_arith) (by omega_arith)]
    exact hfo.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hp.o_scr.symm.sub_left (sub_word fC (by omega_arith))) (by decide)
  · rw [Proof.Sha3.stateAt_congr fun j hj => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hj,
      Proof.Sha3.stateAt_congr fun j hj => hfo.bytes (R := stR s₀) (by simpa using hp.st_o) (by simp) hj]
    exact hI.state
  · rw [hfc.bytes (R := oR s₀) (by simpa using hp.o_scr) (by show outn s₀ ≤ 2 ^ 64; omega_arith)
      (show j < outn s₀ by omega_arith), hm₄]
    by_cases e : i ≤ j
    · rw [show oA s₀ + BitVec.ofNat 64 j = oA s₀ + BitVec.ofNat 64 i + BitVec.ofNat 64 (j - i) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' e],
        Proof.Sha3.writeW64_byte _ _ _ (by omega_arith), readW64_byte _ _ (by omega_arith),
        BitVec.add_assoc, ← BitVec.ofNat_add,
        ← byteOf_stateAt s.mem (stA s₀) (show pos + (j - i) < 200 by omega_arith), hI.state]
      obtain ⟨d, m⟩ := div_mod_eq (k := k) hr₀ (show pos + (j - i) < rt s₀ by omega_arith)
      rw [show pos₀ s₀ + j = rt s₀ * k + (pos + (j - i)) by have := hI.hi; omega_arith, d, m]
    · rw [writeW64_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact hI.out j (by omega_arith)
  · rw [z₉, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, hI.edi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      VG.Proof.Sha256.X86.Stream.sub_ofNat (by omega_arith), Nat.sub_sub,
      VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega_arith)]

/-- A turn: of eight bytes where the block and the output have eight left,
of one byte otherwise. -/
theorem turn_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hR : Ready s₀ i k pos s)
    (hlt : pos < rt s₀) (hi : i < outn s₀) :
    WP isa (turn (squeezeByte ++ storeVars ++ step) (squeezeWord ++ storeVars8 ++ step8)) s fun s' =>
      ∃ n, 0 < n ∧ i + n ≤ outn s₀ ∧ Inv s₀ (i + n) k (pos + n) s' ∧
        s'.zf = some (decide (outn s₀ - (i + n) = 0)) := by
  unfold turn
  refine WP.seq (WP.mono (room_ok hp hR) fun s₁ ⟨hR₁, hc₁⟩ => ?_)
  refine WP.ite (decide (rt s₀ < pos + 8)) (by rw [show isa.eval .b s₁ = s₁.cf from rfl, hc₁])
    (fun _ => WP.mono (store_ok hp hR₁ hlt hi) fun s' h => ⟨1, by decide, hi, h⟩) (fun hb => ?_)
  simp only [decide_eq_false_iff_not] at hb
  refine WP.seq (WP.mono (left_ok hR₁) fun s₂ ⟨hR₂, hc₂⟩ => ?_)
  refine WP.ite (decide (outn s₀ - i < 8)) (by rw [show isa.eval .b s₂ = s₂.cf from rfl, hc₂])
    (fun _ => WP.mono (store_ok hp hR₂ hlt hi) fun s' h => ⟨1, by decide, hi, h⟩) (fun hb' => ?_)
  simp only [decide_eq_false_iff_not] at hb'
  exact WP.mono (word_ok hp hR₂ (by omega_arith) (by omega_arith)) fun s' h =>
    ⟨8, by decide, by omega_arith, h⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {i k pos : Nat} {s : State} (hI : Inv s₀ i k pos s)
    (hi : i < outn s₀) :
    WP isa squeezeBody s fun s' => ∃ n k' pos', 0 < n ∧ i + n ≤ outn s₀ ∧ Inv s₀ (i + n) k' pos' s' ∧
      s'.zf = some (decide (outn s₀ - (i + n) = 0)) := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold squeezeBody
  refine WP.seq (WP.mono (check_ok hp hI) fun s₁ ⟨hI₁, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k' pos', Inv s₀ i k' pos' s ∧ pos' < rt s₀) ?_
    fun s₂ ⟨k', pos', hI₂, hlt⟩ => WP.seq (WP.mono (load_ok hp hI₂) fun s₃ hR₃ =>
      WP.mono (turn_ok hp hR₃ hlt hi) fun s' ⟨n, h0, hle, h⟩ => ⟨n, k', pos' + n, h0, hle, h⟩))
  unfold next
  refine WP.ite (decide (pos = rt s₀)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.mono (permute_ok hp hI₁) fun s' h => ⟨k + 1, 0, h, hr₀⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil ⟨k, pos, hI₁, by have := hI.pos_le; omega_arith⟩

/-! ## The epilogue -/

theorem epilogue_eq : epilogue = .mov .eax (.mem (at_ .ebp 528)) :: .alu .sub .eax (.reg .ebx) ::
    .mov .ecx (.reg .ebp) :: (Spill.restoreCode .ecx saved ++ []) := rfl

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {k pos : Nat} {s : State} (hI : Inv s₀ (outn s₀) k pos s) :
    WP isa (.block epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.squeezeX86.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpos : pos ≤ rt s₀ := hI.pos_le
  rw [epilogue_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega_arith))
    fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_mov fun s₃ u₃ => ?_
  obtain e₃ : s₃.gpr .ecx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.ebp]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr]
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esp]
  refine Spill.restore_ok saved (by decide)
    (fun p h => by rw [e₃]; exact hp.scr_in w₃ (by have := saved_bound p h; omega_arith))
    (by rw [e₃, m₃]; exact hI.saved) fun s₇ r₇ => ?_
  obtain m₇ : s₇.mem = s.mem := by rw [r₇.mem, m₃]
  obtain hax : (s₇.gpr .eax).toNat = pos := by
    rw [r₇.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.ptr, hI.ebx, add_sub_self,
      VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_arith)]
  refine WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_, by rw [hax]; exact hpos, fun d => ?_⟩
  · exact r₇.abi (by decide) (by decide) esp₃ r hr
  · rw [m₇]
    exact hI.frame.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_o, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega_arith)
        hp.sp_lo⟩) (by decide)
  · show bytesAt s₇.mem (oA s₀) (outn s₀) = Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀) (outn s₀)
    rw [m₇]
    refine List.ext_getElem (by rw [length_squeezeFrom hr₀ (by omega_arith)]; simp [bytesAt]) fun j h₁ _ => ?_
    obtain hj : j < outn s₀ := by simpa [bytesAt] using h₁
    rw [squeezeFrom_getElem hr₀ (by omega_arith) _ hj]
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    exact hI.out j hj
  · show Spec.Sha3.squeezeFrom (rt s₀) (stateAt s₇.mem (stA s₀)) (s₇.gpr .eax).toNat d =
      Spec.Sha3.squeezeFrom (rt s₀) (S₀ s₀) (pos₀ s₀ + outn s₀) d
    rw [m₇, hI.state, hax, squeezeFrom_iterF hr₀ (by omega_arith), ← hI.hi]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa squeeze s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.squeezeX86.post s₀ s' := by
  unfold squeeze
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ k pos, Inv s₀ (outn s₀) k pos s) ?_
    fun s₂ ⟨k, pos, hI₂⟩ => epilogue_ok hp hI₂)
  refine WP.ite (decide (outn s₀ = 0)) (by rw [show isa.eval .e s₁ = s₁.zf from rfl, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil ⟨0, pos₀ s₀, by rw [hb]; exact hI⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ i k pos, n = outn s₀ - i ∧ i < outn s₀ ∧ Inv s₀ i k pos s) ?_
      (outn s₀) s₁ ⟨0, 0, pos₀ s₀, by omega_arith, by omega_arith, hI⟩
    rintro n s ⟨i, k, pos, rfl, hi, hI⟩
    refine WP.mono (body_ok hp hI hi) fun s' ⟨m, k', pos', hm, hle, hI', hz'⟩ => ?_
    by_cases hl : outn s₀ - (i + m) = 0
    · exact .inl ⟨by simp [eval, hz', hl], k', pos', by rwa [show i + m = outn s₀ by omega_arith] at hI'⟩
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega_arith, i + m, k', pos', rfl, by omega_arith, hI'⟩

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 3), which are public; the words of `state`,
`out` and `scratch` are the base addresses of regions 0, 1 and 2 (`out` of
unknown length). -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 0, 640, 24], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 24)], wbases := [(3, 0, 0), (3, 20, 2)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  obtain hst := hp.st_fit; have hsc := hp.scr_fit; have ho := hp.o_fit
  have hs : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.sp_fit
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_o, hp.st_scr, hp.a_st.symm⟩, ⟨hp.o_scr, hp.a_o.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [addr_toNat]; omega_arith
    · simp only [addr_toNat]; omega_arith
    · simp only [addr_toNat]; omega_arith
    · show (addr (s.gpr .esp) 4).toNat + 24 ≤ 2 ^ 32
      rw [addr_eq (by omega_arith), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega_arith
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 3).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 20) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 24) (by omega_arith) (k := 20) (by omega_arith)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    obtain e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_o
    · exact hp.stk_scr
    · exact (arg_stk (n := 24) (by omega_arith) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.squeezeX86.pre s₁) (h₂ : Proof.Sha3.squeezeX86.pre s₂)
    (hpub : Proof.Sha3.squeezeX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, oR, scR, argR, stA, oA, st, op, outn, scr, argAddr, ha 0 (by omega_arith), ha 3 (by omega_arith),
      ha 4 (by omega_arith), ha 5 (by omega_arith), hesp]
  · refine VG.X86.Taint.slotsOk_of_list rfl fun sl hsl => ?_
    simp only [List.mem_singleton] at hsl
    subst hsl; decide
  · intro i k hk
    rw [show τ₀.slots = VG.Slots.ofList [(3, 0, 24)] from rfl, VG.Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, _, hk⟩ := hk
    simp only [List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 24) (by have := hp₁.sp_fit; omega_arith) hk,
      argWord_eq (n := 24) (by have := hp₂.sp_fit; omega_arith) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

/-- Memory holding the arguments `0x1000, 72, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4008 then 72 else if a = 0x4011 then 0x20 else
  if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no output). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩, ⟨0x4004, 24⟩]

theorem sat_pre : Proof.Sha3.squeezeX86.pre sat := by
  obtain a0 : arg sat 0 = 0x1000 := by decide
  obtain a1 : arg sat 1 = 72 := by decide
  obtain a2 : arg sat 2 = 0 := by decide
  obtain a3 : arg sat 3 = 0x2000 := by decide
  obtain a4 : arg sat 4 = 0 := by decide
  obtain a5 : arg sat 5 = 0x3000 := by decide
  obtain e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.squeezeX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem squeeze_verified : Verified X86.target squeeze Proof.Sha3.squeezeX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Squeeze

end

end

/-! ### `Sha3.X86.Stream.Pad`, which the modules that import this one used -/

section

/-!
# The SHA-3 sponge on x86 (32-bit): `pad`

The structure of the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Pad`): two
bytes of the state XORed, then the permutation, with `ebx` and `esi` saved in
the scratch space.
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Stream.Pad

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add wp_subi
  contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32 wp_xorm)
open VG.Proof.Sha3 (Rep xorByte stateAt_xorByte absorb_pad writeW8_apply ne_of_lt200 rate_bounds
  contains_offset)
open VG.Spec.Sha3 (stateAt keccakF rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scR s₀, argR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 24 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.padX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  obtain e := stk_eq h12
  exact ⟨h1, h2, h3, h4, h5, h6, h7, by show (below _ _).Disjoint _; rw [e]; exact h8,
    by show (below _ _).Disjoint _; rw [e]; exact h9, h10, h11, h12, h13, h14, h15⟩

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 20⟩ := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 72 ≤ rt s₀ ∧ rt s₀ ≤ 168 := rate_bounds hp.rate

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega_arith) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀, scR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 24) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  obtain fit : (E s₀).toNat + 4 + 20 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_arith
  obtain hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (argR_eq s₀ ▸ hp.a_st).sub_left hs
  · exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega_arith) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

theorem st_in {s : State} (hw : s.wr = s₀.wr) {j : Nat} (hj : j < 200) :
    InRegions s.wr (stA s₀ + BitVec.ofNat 64 j) 1 :=
  ⟨stR s₀, by simp [hw, hp.wr], contains_offset (by omega_arith) (by omega_arith)⟩

/-- The words of the scratch space beyond what the permutation uses. -/
theorem hi_sep {d : Nat} (hd₁ : 512 ≤ d) (hd : d + 4 ≤ 640) :
    ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  obtain hs := sub_word (N := 640) hp.scr_fit hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hs
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega_arith)] at h₁
    obtain hE := addr_toNat (scr s₀)
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
  · exact hp.stk_scr.symm.sub_left hs

/-- A word of the scratch space is unchanged by a write to the state. -/
theorem scr_st (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < 200) (v : Byte) :
    (m.writeW (stA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.st_scr.symm.sep (contains_addr hd (by omega_arith) hp.scr_fit)
    (contains_offset (by omega_arith) (by omega_arith))) (by decide)

end Pre

/-! ## The two bytes -/

/-- What holds after XORing the two bytes into the state. -/
structure Mid (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ecx : s.gpr .ecx = st s₀
  esi : s.gpr .esi = scr s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  esp : s.gpr .esp = E s₀
  sv_ebx : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx
  sv_esi : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  state : stateAt s.mem (stA s₀) =
    xorByte (xorByte (stateAt s₀.mem (stA s₀)) (pos s₀) ((arg s₀ 3).setWidth 8)) (rt s₀ - 1) 0x80

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  VG.Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem xor_0x80 (b : Byte) : (b.setWidth 32 ^^^ (0x80 : BitVec 32)).setWidth 8 = b ^^^ 0x80 := by
  rw [xor_low]; rfl

theorem bytes_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block padBytes) s₀ (Mid s₀) := by
  obtain fC := hp.scr_fit; have fS := hp.st_fit
  have hs : (E s₀).toNat + 24 ≤ 2 ^ 32 := hp.sp_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hpl := hp.pos_lt
  unfold padBytes
  refine wp_movm (a := addr (E s₀) 20) (ea_at _ _ _) (hp.arg_in rfl (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 512) (by rw [ea_at, e1]) (hp.scr_out u₁.wr (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 516) (by rw [ea_at, u₂.gpr, e1])
    (hp.scr_out (by rw [u₂.wr, u₁.wr]) (by omega_arith)) fun s₃ u₃ => ?_
  obtain w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain m₃ : s₃.mem = (s₀.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.other .ebx (by decide), u₁.other .esi (by decide)]
  obtain f₃ : Frame [scR s₀] s₀.mem s₃.mem := by
    rw [m₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_arith) (by omega_arith) fC)
  obtain f₃' : Frame [stR s₀, scR s₀] s₀.mem s₃.mem := f₃.mono (by simp)
  refine wp_mov fun s₄ u₄ => ?_
  obtain k₄ : ∀ r, r ≠ .eax → r ≠ .esi → s₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₄.other r h', u₃.gpr, u₂.gpr, u₁.other r h]
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  refine wp_movm (a := addr (E s₀) 4) (by rw [ea_at, k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₄.wr, w₃]) (by omega_arith) (by omega_arith)) fun s₅ u₅ => ?_
  refine wp_movm (a := addr (E s₀) 8) (by rw [ea_at, u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₅.wr, u₄.wr, w₃]) (by omega_arith) (by omega_arith)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (E s₀) 12) (by rw [ea_at, u₆.other _ (by decide), u₅.other _ (by decide),
    k₄ _ (by decide) (by decide)]) (hp.arg_in (by rw [u₆.wr, u₅.wr, u₄.wr, w₃]) (by omega_arith) (by omega_arith))
    fun s₇ u₇ => ?_
  refine wp_add fun s₈ u₈ => ?_
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  obtain w₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, w₃]
  obtain r₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain c₅ : s₅.gpr .ecx = st s₀ := by rw [u₅.gpr, m₄, hp.arg_keep f₃' (by omega_arith) (by omega_arith)]; rfl
  obtain a₆ : s₆.gpr .eax = arg s₀ 1 := by
    rw [u₆.gpr, u₅.mem, m₄, hp.arg_keep f₃' (by omega_arith) (by omega_arith)]; rfl
  obtain d₈ : s₈.gpr .edx = st s₀ + BitVec.ofNat 32 (pos s₀) := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c₅, u₆.mem, u₅.mem, m₄,
      hp.arg_keep f₃' (by omega_arith) (by omega_arith), BitVec.add_comm]
    show _ = _ + BitVec.ofNat 32 (arg s₀ 2).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  obtain hpA : addr (s₈.gpr .edx) 0 = stA s₀ + BitVec.ofNat 64 (pos s₀) := by
    rw [d₈]; exact ptr_addr (by omega_arith)
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 (pos s₀)) (by rw [ea_at, hpA])
    (by rw [r₈, w₈, hp.rd, List.nil_append]; exact hp.st_in rfl (by omega_arith)) fun s₉ u₉ => ?_
  refine wp_xorm (b := .esp) (B := E s₀) (o := 16)
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.arg_in (by rw [u₉.wr, w₈]) (by omega_arith) (by omega_arith)) fun s₁₀ u₁₀ => ?_
  refine wp_store8 (r := .bl) (a := stA s₀ + BitVec.ofNat 64 (pos s₀))
    (by rw [ea_at, u₁₀.other _ (by decide), u₉.other _ (by decide), hpA])
    (by rw [u₁₀.wr, u₉.wr, w₈]; exact hp.st_in rfl (by omega_arith)) fun s₁₁ u₁₁ => ?_
  obtain m₁₁ : s₁₁.mem = s₃.mem.writeW (stA s₀ + BitVec.ofNat 64 (pos s₀))
      (s₃.mem (stA s₀ + BitVec.ofNat 64 (pos s₀)) ^^^ (arg s₀ 3).setWidth 8) := by
    rw [u₁₁.mem, show Reg8.bl.reg = Reg.ebx from rfl, u₁₀.gpr, u₉.gpr, u₁₀.mem, u₉.mem, m₈, xor_low,
      hp.arg_keep f₃' (by omega_arith) (by omega_arith)]
    rfl
  refine wp_mov fun s₁₂ u₁₂ => wp_add fun s₁₃ u₁₃ => wp_subi fun s₁₄ u₁₄ _ => ?_
  obtain d₁₄ : s₁₄.gpr .edx = st s₀ + BitVec.ofNat 32 (rt s₀ - 1) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₂.other .eax (by decide), u₁₁.gpr, u₁₀.other .ecx (by decide),
      u₁₀.other .eax (by decide), u₉.other .ecx (by decide), u₉.other .eax (by decide),
      u₈.other .ecx (by decide), u₈.other .eax (by decide), u₇.other .ecx (by decide),
      u₇.other .eax (by decide), u₆.other .ecx (by decide), c₅, a₆]
    have h72 : 72 ≤ (arg s₀ 1).toNat := hr₀
    show _ = _ + BitVec.ofNat 32 ((arg s₀ 1).toNat - 1)
    exact Offset.add_sub_one32 _ _ (by omega_arith)
  obtain hpB : addr (s₁₄.gpr .edx) 0 = stA s₀ + BitVec.ofNat 64 (rt s₀ - 1) := by
    rw [d₁₄]; exact ptr_addr (by omega_arith)
  obtain w₁₄ : s₁₄.wr = s₀.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, w₈]
  refine wp_movzx8 (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) (by rw [ea_at, hpB])
    (by
      rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, r₈, w₁₄, hp.rd, List.nil_append]
      exact hp.st_in rfl (by omega_arith)) fun s₁₅ u₁₅ => ?_
  refine wp_xori fun s₁₆ u₁₆ => ?_
  refine wp_store8 (r := .bl) (a := stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
    (by rw [ea_at, u₁₆.other _ (by decide), u₁₅.other _ (by decide), hpB])
    (by rw [u₁₆.wr, u₁₅.wr, w₁₄]; exact hp.st_in rfl (by omega_arith)) fun s₁₇ u₁₇ => WP.block_nil ?_
  obtain m₁₄ : s₁₄.mem = s₁₁.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem]
  obtain m₁₇ : s₁₇.mem = s₁₁.mem.writeW (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1))
      (s₁₁.mem (stA s₀ + BitVec.ofNat 64 (rt s₀ - 1)) ^^^ 0x80) := by
    rw [u₁₇.mem, show Reg8.bl.reg = Reg.ebx from rfl, u₁₆.gpr, u₁₅.gpr, u₁₆.mem, u₁₅.mem, m₁₄, xor_0x80]
  obtain f₁₇ : Frame [stR s₀, scR s₀] s₃.mem s₁₇.mem := by
    rw [m₁₇, m₁₁]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (contains_offset (by omega_arith) (by omega_arith))).writeW
      (List.mem_cons_self ..) _ (contains_offset (by omega_arith) (by omega_arith))
  obtain k₁₇ : ∀ r, r ∉ [Reg.eax, .ebx, .ecx, .edx, .esi] → s₁₇.gpr r = s₀.gpr r := fun r hr => by
    have ⟨a, b, c, d, e⟩ : r ≠ .eax ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .esi := by simpa using hr
    rw [u₁₇.gpr, u₁₆.other r b, u₁₅.other r b, u₁₄.other r d, u₁₃.other r d, u₁₂.other r d, u₁₁.gpr,
      u₁₀.other r b, u₉.other r b, u₈.other r d, u₇.other r d, u₆.other r a, u₅.other r c, k₄ r a e]
  obtain hsc : ∀ d, d + 4 ≤ 640 → s₁₇.mem.readW (addr (scr s₀) d) 32 = s₃.mem.readW (addr (scr s₀) d) 32 :=
    fun d hd => by rw [m₁₇, hp.scr_st _ hd (by omega_arith), m₁₁, hp.scr_st _ hd (by omega_arith)]
  refine ⟨?_, by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄], ?_, ?_, k₁₇ _ (by decide), k₁₇ _ (by decide),
    k₁₇ _ (by decide), ?_, ?_, f₃'.trans f₁₇, ?_⟩
  · rw [u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, r₈]
  · rw [u₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), c₅]
  · rw [u₁₇.gpr, u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, e1]
  · rw [hsc _ (by omega_arith), m₃, word_sep (N := 640) fC (by omega_arith) (by omega_arith) (by omega_arith),
      Mem.readW_writeW_self32]
  · rw [hsc _ (by omega_arith), m₃, Mem.readW_writeW_self32]
  · have e₃ : stateAt s₃.mem (stA s₀) = stateAt s₀.mem (stA s₀) :=
      Proof.Sha3.stateAt_congr fun i hi => f₃.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
    rw [← e₃, ← stateAt_xorByte (m := s₃.mem) (m' := s₁₁.mem) (by omega_arith)
      (by rw [m₁₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [m₁₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi (by omega_arith) hne))])]
    exact stateAt_xorByte (by omega_arith)
      (by rw [m₁₇, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
      (fun i hi hne => by
        rw [m₁₇, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt200 hi (by omega_arith) hne))])

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa pad s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.padX86.post s₀ s' := by
  obtain fC := hp.scr_fit; have fS := hp.st_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have h72 : 72 ≤ (arg s₀ 1).toNat := hr₀
  have h168 : (arg s₀ 1).toNat ≤ 168 := hr₁
  unfold pad
  refine WP.seq (WP.mono (bytes_ok hp) fun s₁ h => ?_)
  refine WP.seq (permuteCall_ok (st := .ecx) (scr := .esi) (by decide) (by decide) h.esp h.ecx h.esi
    hp.sp_lo fS (by omega_arith) (hp.st_scr.sub_right (Region.sub_prefix (by omega_arith))) hp.stk_st
    (hp.stk_scr.sub_right (Region.sub_prefix (by omega_arith))) (by rw [h.wr, hp.wr]; simp)
    (by rw [h.wr, hp.wr]; simp) fun s₂ rd₂ wr₂ cs₂ f₂ e₂ => ?_)
  obtain w₂ : s₂.wr = s₀.wr := wr₂.trans h.wr
  obtain hsi : s₂.gpr .esi = scr s₀ := by rw [cs₂ _ (by decide), h.esi]
  refine wp_movm (a := addr (scr s₀) 512) (by rw [ea_at, hsi]) (hp.scr_in w₂ (by omega_arith)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 516) (by rw [ea_at, u₃.other _ (by decide), hsi])
    (hp.scr_in (by rw [u₃.wr, w₂]) (by omega_arith)) fun s₄ u₄ => WP.block_nil ?_
  obtain m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain hk : ∀ d, 512 ≤ d → d + 4 ≤ 640 → s₂.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 :=
    fun d h1 h2 => f₂.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _)
      (hp.hi_sep h1 h2) (by decide)
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun msg hR hm => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.gpr, hk _ (by omega_arith) (by omega_arith), h.sv_ebx]
    · rw [u₄.gpr, u₃.mem, hk _ (by omega_arith) (by omega_arith), h.sv_esi]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.edi]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.ebp]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), cs₂ _ (by decide), h.esp]
  · rw [m₄]
    obtain hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s₂.mem :=
      (h.frame.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp).trans (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
        · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
    exact hf.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega_arith) hp.sp_lo⟩)
      (by decide)
  · rw [m₄, show (arg s₀ 0).setWidth 64 = stA s₀ from rfl, e₂, h.state,
      absorb_pad (by omega_arith) (by omega_arith), ← hm, show Rep (rt s₀) msg = stateAt s₀.mem (stA s₀) from hR.symm]

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 2), which are public; the words of `state` and
`scratch` are the base addresses of regions 0 and 1. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 640, 20], bases := [(.esp, 2, 4)],
    slots := [(2, 0, 20)], wbases := [(2, 0, 0), (2, 16, 1)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  have hs : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp.sp_fit
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_scr, hp.a_st.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [addr_toNat]; omega_arith
    · simp only [addr_toNat]; omega_arith
    · show (addr (s.gpr .esp) 4).toNat + 20 ≤ 2 ^ 32
      rw [addr_eq (by omega_arith), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega_arith
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 2).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 16) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 20) (by omega_arith) (k := 16) (by omega_arith)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    obtain e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_scr
    · exact (arg_stk (n := 20) (by omega_arith) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.padX86.pre s₁) (h₂ : Proof.Sha3.padX86.pre s₂)
    (hpub : Proof.Sha3.padX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, argR, stA, st, scr, argAddr, ha 0 (by omega_arith), ha 4 (by omega_arith), hesp]
  · refine VG.X86.Taint.slotsOk_of_list rfl fun sl hsl => ?_
    simp only [List.mem_singleton] at hsl
    subst hsl; decide
  · intro i k hk
    rw [show τ₀.slots = VG.Slots.ofList [(2, 0, 20)] from rfl, VG.Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, _, hk⟩ := hk
    simp only [List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 20) (by have := hp₁.sp_fit; omega_arith) hk,
      argWord_eq (n := 20) (by have := hp₂.sp_fit; omega_arith) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

/-- Memory holding the arguments `0x1000, 72, 0, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4008 then 72 else if a = 0x4015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩, ⟨0x4004, 20⟩]

theorem sat_pre : Proof.Sha3.padX86.pre sat := by
  obtain a0 : arg sat 0 = 0x1000 := by decide
  obtain a1 : arg sat 1 = 72 := by decide
  obtain a2 : arg sat 2 = 0 := by decide
  obtain a4 : arg sat 4 = 0x3000 := by decide
  obtain e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.padX86, a0, a1, a2, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem pad_verified : Verified X86.target pad Proof.Sha3.padX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Pad

end

end

/-!
# The SHA-3 sponge on x86 (32-bit): `absorb`

The structure of the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Absorb`), with
`state` in `ebx`, `scratch` in `ebp`, `data` in `esi`, the bytes left in
`edi`, and `state + pos` and `rate` in the scratch space. A turn of the loop
XORs eight bytes of data into the state (`word_ok`) where the block and the
data have eight left, and one byte (`byte_ok`) otherwise (`turn_ok`): either
leaves the state with those bytes XORed in at the position (`Turned`), and
what follows, the test for the end of the block and the permutation, is the
same for both (`Proof.Sha3.rep_append`).
-/

@[expose] public section

namespace VG.Proof.Sha3.X86.Stream.Absorb

open VG VG.X86 VG.Impl.Sha3.X86.Stream
open VG.Impl.Sha512.X86 (at_)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movm wp_movzx8 wp_store wp_store8 wp_add
  wp_addi wp_sub wp_subi wp_cmp wp_cmpi wp_test contains_addr addr_toNat)
open VG.Proof.Sha3.X86 (permuteCall_ok reg32 wp_xorm)
open VG.Proof.Sha3 (Rep rep_append xorAt xorAt_single xorByte stateAt_xorByte bytesAt_length writeW8_apply
  rate_bounds contains_offset)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev rt : Nat := (arg s₀ 1).toNat
abbrev pos : Nat := (arg s₀ 2).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 200⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 640⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 12
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (addr (scr s₀)) s₀.gpr saved

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (stA s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀, argR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_d : (argR s₀).Disjoint (dR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 200 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 640 ≤ 2 ^ 32
  sp_lo : 12 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  obtain e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19, h20, h21⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem argR_eq (s₀ : State) : argR s₀ = ⟨addr (E s₀) 4, 24⟩ := rfl

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem rt_pos : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  have := rate_bounds hp.rate; omega_using [this]

theorem arg_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) d) 4 :=
  ⟨argR s₀, by simp [hw, hp.wr], by rw [argR_eq s₀]; exact arg_contains (by have := hp.sp_fit; omega_using [this]) h₁ h₂⟩

/-- The argument words are never written. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d)
    (h₂ : d + 4 ≤ 28) : m.readW (addr (E s₀) d) 32 = s₀.mem.readW (addr (E s₀) d) 32 := by
  obtain fit : (E s₀).toNat + 4 + 24 ≤ 2 ^ 32 := by have := hp.sp_fit; omega_using [this]
  obtain hs := arg_word fit h₁ h₂
  refine hf.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (argR_eq s₀ ▸ hp.a_st).sub_left hs
  · exact (argR_eq s₀ ▸ hp.a_scr).sub_left hs
  · exact (arg_stk fit hp.sp_lo).sub_left hs

theorem scr_out {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hw, hp.wr], contains_addr hd (by omega_using []) hp.scr_fit⟩

theorem scr_in {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 640) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  let ⟨r, hr, hc⟩ := hp.scr_out hw hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A write within the scratch space. -/
theorem frame_scr {rs : List Region} (hr : scR s₀ ∈ rs) {m : Mem} (hf : Frame rs s₀.mem m) {d : Nat}
    (hd : d + 4 ≤ 640) (v : BitVec 32) : Frame rs s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  hf.writeW hr _ (contains_addr hd (by omega_using []) hp.scr_fit)

/-- The words of the scratch space beyond what the permutation uses. -/
theorem hi_sep {d : Nat} (hd₁ : 512 ≤ d) (hd : d + 4 ≤ 640) :
    ∀ r ∈ [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀], Region.Disjoint ⟨addr (scr s₀) d, 4⟩ r := by
  have := hp.scr_fit
  obtain hs := sub_word (N := 640) hp.scr_fit hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left hs
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    rw [addr_eq (by omega_using [hd, this])] at h₁
    obtain hE := addr_toNat (scr s₀)
    generalize (scr s₀).setWidth 64 = b at *
    bv_omega
  · exact hp.stk_scr.symm.sub_left hs

/-- A word of the scratch space is unchanged by a write to the state. -/
theorem scr_st (m : Mem) {d : Nat} (hd : d + 4 ≤ 640) {j : Nat} (hj : j < 200) (v : Byte) :
    (m.writeW (stA s₀ + BitVec.ofNat 64 j) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (hp.st_scr.symm.sep (contains_addr hd (by omega_using []) hp.scr_fit)
    (contains_offset (by omega_using [hj]) (by omega_using [hj]))) (by decide)

end Pre

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 528 := by decide

theorem saved_fits : Spill.Fits 528 saved := by decide

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 528 → m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32) :
    Saved s₀ m' :=
  hs.of_readW fun p hp' => hk _ (saved_bound p hp').1 (saved_bound p hp').2

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = E s₀
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  edi : s.gpr .edi = BitVec.ofNat 32 (len s₀ - c)
  rate : s.mem.readW (addr (scr s₀) rOff) 32 = arg s₀ 1
  frame : Frame [stR s₀, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  ptr : s.mem.readW (addr (scr s₀) pOff) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (stA s₀) = Rep (rt s₀) (msg ++ D s₀ c)

theorem Common.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s) (u : Fupd s s') :
    Common s₀ c s' where
  c_le := h.c_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  ebx := by rw [u.gpr]; exact h.ebx
  ebp := by rw [u.gpr]; exact h.ebp
  esp := by rw [u.gpr]; exact h.esp
  esi := by rw [u.gpr]; exact h.esi
  edi := by rw [u.gpr]; exact h.edi
  rate := by rw [u.mem]; exact h.rate
  frame := by rw [u.mem]; exact h.frame
  saved := by rw [u.mem]; exact h.saved

/-- A call of the permutation keeps what holds throughout. -/
theorem Common.after_call {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [reg32 (st s₀) 200, reg32 (scr s₀) 512, stkR s₀] s.mem s'.mem) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hcs _ (by decide)]; exact h.ebx
  ebp := by rw [hcs _ (by decide)]; exact h.ebp
  esp := by rw [hcs _ (by decide)]; exact h.esp
  esi := by rw [hcs _ (by decide)]; exact h.esi
  edi := by rw [hcs _ (by decide)]; exact h.edi
  rate := by
    rw [hf.readW (Region.contains_self _ _) (hp.hi_sep (by decide) (by decide)) (by decide)]; exact h.rate
  frame := h.frame.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  saved := h.saved.keep fun d h1 h2 => hf.readW (Region.contains_self _ _) (hp.hi_sep h1 (by omega_using [h2]))
    (by decide)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := len_lt s₀; show len s₀ ≤ 2 ^ 64; omega_using [this]) hi

/-! ## The prologue -/

theorem setup_eq : setup = .mov .eax (.mem (at_ .esp 24)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .esp 12)),
    .alu .add .ecx (.reg .ebx), .store (at_ .ebp 528) .ecx, .mov .ecx (.mem (at_ .esp 8)),
    .store (at_ .ebp 532) .ecx, .mov .esi (.mem (at_ .esp 16)), .mov .edi (.mem (at_ .esp 20)),
    .alu .test .edi (.reg .edi)] : List Instr)) := rfl

/-- The memory after saving the registers. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (scr s₀)) s₀.gpr saved

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) s₀ fun s => Inv s₀ 0 s ∧ s.zf = some (decide (len s₀ = 0)) := by
  have fC := hp.scr_fit
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  rw [setup_eq]
  refine wp_movm (a := addr (E s₀) 24) (ea_at _ _ _) (hp.arg_in rfl (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e1]; exact hp.scr_out u₁.wr (by have := saved_bound p h; omega_using [this])) fun s₅ u₅ => ?_
  obtain g₅ : ∀ r, r ≠ .eax → s₅.gpr r = s₀.gpr r := fun r h => by rw [u₅.gpr, u₁.other r h]
  obtain m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, e1, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain w₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  obtain r₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  obtain hsc : scR s₀ ∈ [scR s₀] := List.mem_singleton_self _
  obtain f₅ : Frame [scR s₀] s₀.mem s₅.mem := by
    rw [m₅]
    exact Spill.saveMem_frame hsc _ _ _ _ fun p h =>
      contains_addr (by have := saved_bound p h; omega_using [this]) (by omega_using []) fC
  obtain sv₅ : Saved s₀ s₅.mem := by
    rw [m₅]; exact Spill.saveMem_saved_addr _ _ saved_fits (by omega_using [fC])
  refine wp_mov fun s₆ u₆ => ?_
  refine wp_movm (a := addr (E s₀) 4) (by rw [ea_at, u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₆.wr, w₅]) (by omega_using []) (by omega_using [])) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (E s₀) 12) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in (by rw [u₇.wr, u₆.wr, w₅]) (by omega_using []) (by omega_using [])) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  obtain e5 : s₅.gpr .eax = scr s₀ := by rw [u₅.gpr, e1]
  obtain hb₉ : s₉.gpr .ebp = scr s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e5]
  obtain m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
  obtain hst : s₇.gpr .ebx = st s₀ := by
    rw [u₇.gpr, u₆.mem, hp.arg_keep (f₅.mono (by simp)) (by omega_using []) (by omega_using [])]; rfl
  obtain hpos : s₉.gpr .ecx = st s₀ + BitVec.ofNat 32 (pos s₀ % rt s₀) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), hst, u₇.mem, u₆.mem, hp.arg_keep (f₅.mono (by simp)) (by omega_using []) (by omega_using []),
      Nat.mod_eq_of_lt hp.pos_lt, BitVec.add_comm]
    show _ = _ + BitVec.ofNat 32 (arg s₀ 2).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₉])
    (hp.scr_out (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_using [])) fun s₁₀ u₁₀ => ?_
  obtain f₁₀ : Frame [scR s₀] s₀.mem s₁₀.mem := by
    rw [u₁₀.mem, u₉.mem, m₈]; exact hp.frame_scr hsc f₅ (by omega_using []) _
  refine wp_movm (a := addr (E s₀) 8) (by rw [ea_at, u₁₀.gpr, u₉.other _ (by decide),
    u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_using []) (by omega_using [])) fun s₁₁ u₁₁ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₁₁.other _ (by decide), u₁₀.gpr, hb₉])
    (hp.scr_out (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]) (by omega_using [])) fun s₁₂ u₁₂ => ?_
  obtain f₁₂ : Frame [scR s₀] s₀.mem s₁₂.mem := by
    rw [u₁₂.mem, u₁₁.mem]; exact hp.frame_scr hsc f₁₀ (by omega_using []) _
  obtain hw₁₂ : s₁₂.wr = s₀.wr := by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, w₅]
  refine wp_movm (a := addr (E s₀) 16) (by rw [ea_at, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr,
    u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    g₅ _ (by decide)]) (hp.arg_in hw₁₂ (by omega_using []) (by omega_using [])) fun s₁₃ u₁₃ => ?_
  refine wp_movm (a := addr (E s₀) 20) (by rw [ea_at, u₁₃.other _ (by decide), u₁₂.gpr,
    u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
    u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide)])
    (hp.arg_in (by rw [u₁₃.wr, hw₁₂]) (by omega_using []) (by omega_using [])) fun s₁₄ u₁₄ => ?_
  refine wp_test fun s₁₅ u₁₅ z₁₅ => WP.block_nil ?_
  -- The registers and memory at the end.
  obtain g : ∀ r, r ∉ [Reg.eax, .ebp, .ebx, .ecx, .esi, .edi] → s₁₅.gpr r = s₀.gpr r := fun r hr => by
    have ⟨a, b, c', d, e, f⟩ : r ≠ .eax ∧ r ≠ .ebp ∧ r ≠ .ebx ∧ r ≠ .ecx ∧ r ≠ .esi ∧ r ≠ .edi := by
      simpa using hr
    rw [u₁₅.gpr, u₁₄.other r f, u₁₃.other r e, u₁₂.gpr, u₁₁.other r d, u₁₀.gpr, u₉.other r d,
      u₈.other r d, u₇.other r c', u₆.other r b, g₅ r a]
  obtain hm : s₁₅.mem = s₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  obtain hm₁₂ : s₁₂.mem = (s₁₀.mem.writeW (addr (scr s₀) 532) (s₁₁.gpr .ecx)) := by
    rw [u₁₂.mem, u₁₁.mem]
  obtain hrate : s₁₁.gpr .ecx = arg s₀ 1 := by
    rw [u₁₁.gpr, hp.arg_keep (f₁₀.mono (by simp)) (by omega_using []) (by omega_using [])]; rfl
  obtain hdi : s₁₄.gpr .edi = arg s₀ 4 := by
    rw [u₁₄.gpr, u₁₃.mem, hp.arg_keep (f₁₂.mono (by simp)) (by omega_using []) (by omega_using [])]; rfl
  refine ⟨⟨⟨Nat.zero_le _, ?_, by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, hw₁₂], ?_, ?_, g .esp (by decide), ?_, ?_,
    ?_, by rw [hm]; exact f₁₂.mono (by simp), ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩, ?_⟩
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, r₅]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hst]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide),
      u₁₀.gpr, hb₉]
  · rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.gpr, hp.arg_keep (f₁₂.mono (by simp)) (by omega_using []) (by omega_using []), BitVec.add_zero]
    rfl
  · rw [u₁₅.gpr, hdi, Nat.sub_zero]; simp [len]
  · rw [hm, hm₁₂, show rOff = 532 from rfl, Mem.readW_writeW_self32, hrate]
  · rw [hm, hm₁₂]
    refine sv₅.keep fun d h1 h2 => ?_
    rw [sep _ _ d 532 (by omega_using [h2]) (by omega_using []) (by omega_using [h2]), u₁₀.mem, u₉.mem, m₈,
      sep _ _ d 528 (by omega_using [h2]) (by omega_using []) (by omega_using [h2])]
  · rw [hm, hm₁₂, show pOff = 528 from rfl, sep _ _ 528 532 (by omega_using []) (by omega_using []) (by omega_using []), u₁₀.mem,
      Mem.readW_writeW_self32, Nat.add_zero]
    exact hpos
  · rw [show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs, hm]
    refine Proof.Sha3.stateAt_congr fun i hi => ?_
    exact f₁₂.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · rw [z₁₅, hdi, BitVec.and_self]
    rw [show arg s₀ 4 = BitVec.ofNat 32 (len s₀) by simp [len], VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (len_lt s₀)]

/-! ## One iteration -/

/-- After `loadVars`: the invariant, with `state + pos` in `ecx` and `rate`
in `edx`. -/
structure Ready (s₀ : State) (c : Nat) (s : State) : Prop extends Inv s₀ c s where
  ecx : s.gpr .ecx = st s₀ + BitVec.ofNat 32 ((pos s₀ + c) % rt s₀)
  edx : s.gpr .edx = arg s₀ 1

theorem load_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa (.block loadVars) s (Ready s₀ c) := by
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]; rfl) (hp.scr_in hI.wr (by omega_using []))
    fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) 532) (by rw [ea_at, u₁.other _ (by decide), hI.ebp]; rfl)
    (hp.scr_in (by rw [u₁.wr, hI.wr]) (by omega_using [])) fun s₂ u₂ => WP.block_nil ?_
  obtain g : ∀ r, r ∉ [Reg.ecx, .edx] → s₂.gpr r = s.gpr r := fun r hr => by
    have ⟨a, b⟩ : r ≠ .ecx ∧ r ≠ .edx := by simpa using hr
    rw [u₂.other r b, u₁.other r a]
  obtain hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  exact {
    c_le := hI.c_le
    rd := by rw [u₂.rd, u₁.rd, hI.rd]
    wr := by rw [u₂.wr, u₁.wr, hI.wr]
    ebx := by rw [g _ (by decide), hI.ebx]
    ebp := by rw [g _ (by decide), hI.ebp]
    esp := by rw [g _ (by decide), hI.esp]
    esi := by rw [g _ (by decide), hI.esi]
    edi := by rw [g _ (by decide), hI.edi]
    rate := by rw [hm]; exact hI.rate
    frame := by rw [hm]; exact hI.frame
    saved := by rw [hm]; exact hI.saved
    ptr := by rw [hm]; exact hI.ptr
    repr := by rw [hm]; exact hI.repr
    ecx := by rw [u₂.other _ (by decide), u₁.gpr]; exact hI.ptr
    edx := by rw [u₂.gpr, u₁.mem]; exact hI.rate }

/-- The registers and the memory are as they were, but `eax` and the flags. -/
theorem Ready.congr {s₀ : State} {c : Nat} {s s' : State} (h : Ready s₀ c s)
    (hg : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Ready s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by decide)]; exact h.ebx
  ebp := by rw [hg _ (by decide)]; exact h.ebp
  esp := by rw [hg _ (by decide)]; exact h.esp
  esi := by rw [hg _ (by decide)]; exact h.esi
  edi := by rw [hg _ (by decide)]; exact h.edi
  rate := by rw [hm]; exact h.rate
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  ptr := by rw [hm]; exact h.ptr
  repr := by rw [hm]; exact h.repr
  ecx := by rw [hg _ (by decide)]; exact h.ecx
  edx := by rw [hg _ (by decide)]; exact h.edx

/-- The test for eight bytes left in the block. -/
theorem room_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hR : Ready s₀ c s) :
    WP isa (.block room8) s fun s' =>
      Ready s₀ c s' ∧ s'.mem = s.mem ∧ s'.cf = some (decide (rt s₀ < (pos s₀ + c) % rt s₀ + 8)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  refine wp_mov fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_addi fun s₃ u₃ => wp_cmp fun s₄ u₄ c₄ _ =>
    WP.block_nil ⟨hR.congr (fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr])
      (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]), by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_⟩
  obtain hax : s₃.gpr .eax = BitVec.ofNat 32 ((pos s₀ + c) % rt s₀ + 8) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ebx (by decide), hR.ecx, hR.ebx, add_sub_self]
    exact (BitVec.ofNat_add _ 8).symm
  obtain hdx : s₃.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hR.edx]
    simp [rt]
  rw [c₄, hax, hdx, VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_using [hr₁]),
    VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_using [hr₁, hj])]

/-- The test for eight bytes of data left. -/
theorem left_ok {s₀ : State} {c : Nat} {s : State} (hR : Ready s₀ c s) :
    WP isa (.block [.alu .cmp .edi (.imm 8)]) s fun s' =>
      Ready s₀ c s' ∧ s'.mem = s.mem ∧ s'.cf = some (decide (len s₀ - c < 8)) := by
  obtain hl := len_lt s₀
  refine wp_cmpi fun s₁ u₁ c₁ _ =>
    WP.block_nil ⟨hR.congr (fun r _ => by rw [u₁.gpr]) u₁.mem u₁.rd u₁.wr, u₁.mem, ?_⟩
  rw [c₁, hR.edi, VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega_using [hl])]
  rfl

/-- After a turn of `n` bytes at the position `j` from the state `s`, before
the test for the end of the block. -/
structure Turned (s₀ : State) (c n j : Nat) (s s' : State) : Prop extends Common s₀ (c + n) s' where
  ptr : s'.mem.readW (addr (scr s₀) pOff) 32 = st s₀ + BitVec.ofNat 32 (j + n)
  ecx : s'.gpr .ecx = st s₀ + BitVec.ofNat 32 (j + n)
  edx : s'.gpr .edx = arg s₀ 1
  state : stateAt s'.mem (stA s₀) = xorAt (stateAt s.mem (stA s₀)) j
    (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) n)

theorem bytesAt_one (m : Mem) (p : Addr) : bytesAt m p 1 = [m p] := by simp [bytesAt]

theorem bytesAt_getD (m : Mem) (p : Addr) {n d : Nat} (hd : d < n) :
    (bytesAt m p n).getD d 0 = m (p + BitVec.ofNat 64 d) := by
  simp [bytesAt, hd]

theorem byte_eq : absorbByte ++ storeVars ++ step =
    [.movzx8 .eax (at_ .esi 0), .alu .xor .eax (.mem (at_ .ecx 0)), .store8 (at_ .ecx 0) .al,
      .alu .add .ecx (.imm 1), .store (at_ .ebp 528) .ecx, .store (at_ .ebp 532) .edx,
      .alu .add .esi (.imm 1), .alu .sub .edi (.imm 1)] := rfl

/-- A turn of one byte: the byte of data XORed into the state at the
position. -/
theorem byte_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hR : Ready s₀ c s) :
    WP isa (.block (absorbByte ++ storeVars ++ step)) s (Turned s₀ c 1 ((pos s₀ + c) % rt s₀) s) := by
  have hI := hR.toInv
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain fS := hp.st_fit; have fC := hp.scr_fit; have fD := hp.d_fit
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain e₂ := hR.ecx
  obtain d₂ := hR.edx
  generalize (pos s₀ + c) % rt s₀ = j at hj e₂ ⊢
  rw [byte_eq]
  obtain hdA : addr (dp s₀ + BitVec.ofNat 32 c) 0 = dA s₀ + BitVec.ofNat 64 c := ptr_addr (by omega_using [hc, fD])
  refine wp_movzx8 (a := dA s₀ + BitVec.ofNat 64 c) (by rw [ea_at, hI.esi, hdA])
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_using [hc]) (by omega_using [hc, fD])⟩ fun s₃ u₃ => ?_
  obtain hsA : addr (st s₀ + BitVec.ofNat 32 j) 0 = stA s₀ + BitVec.ofNat 64 j := ptr_addr (by omega_using [hr₁, fS, hj])
  obtain hsin : ∀ n, n ≤ 4 → InRegions s₀.wr (stA s₀ + BitVec.ofNat 64 j) n := fun n hn =>
    ⟨stR s₀, by simp [hp.wr], contains_offset (by omega_using [hr₁, hj, hn]) (by omega_using [hr₁, hj])⟩
  refine wp_xorm (b := .ecx) (B := st s₀ + BitVec.ofNat 32 j) (o := 0) (by rw [u₃.other _ (by decide), e₂])
    (by rw [hsA]; exact VG.Proof.Sha512.X86.mem_rd (by rw [u₃.wr, hI.wr]; exact hsin 4 (by omega_using [])))
    fun s₄ u₄ => ?_
  obtain e₄ : s₄.gpr .ecx = st s₀ + BitVec.ofNat 32 j := by rw [u₄.other _ (by decide), u₃.other _ (by decide), e₂]
  refine wp_store8 (r := .al) (a := stA s₀ + BitVec.ofNat 64 j) (by rw [ea_at, e₄, hsA])
    (by rw [u₄.wr, u₃.wr, hI.wr]; exact hsin 1 (by omega_using [])) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  obtain e₆ : s₆.gpr .ecx = st s₀ + BitVec.ofNat 32 (j + 1) := by
    rw [u₆.gpr, u₅.gpr, e₄, ofNat_add_one]
  obtain hb₆ : s₆.gpr .ebp = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hI.ebp]
  obtain w₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₆]) (hp.scr_out w₆ (by omega_using [])) fun s₇ u₇ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₇.gpr, hb₆])
    (hp.scr_out (by rw [u₇.wr, w₆]) (by omega_using [])) fun s₈ u₈ => ?_
  refine wp_addi fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ _ => WP.block_nil ?_
  -- The memory.
  obtain hv : (s₄.gpr Reg8.al.reg).setWidth 8 =
      s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j) := by
    show (s₄.gpr .eax).setWidth 8 = _
    rw [u₄.gpr, u₃.gpr, u₃.mem, xor_low, hsA, low_byte, hI.data hp hc]
  obtain hm₁ : s₅.mem = s.mem.writeW (stA s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dA s₀ + BitVec.ofNat 64 c) ^^^ s.mem (stA s₀ + BitVec.ofNat 64 j)) := by
    rw [u₅.mem, hv, u₄.mem, u₃.mem]
  obtain hm : s₁₀.mem = (s₅.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (j + 1))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.gpr, u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), d₂, u₇.mem, u₆.mem, e₆]
  obtain hfs : Frame [stR s₀] s.mem s₅.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  obtain hfc : Frame [scR s₀] s₅.mem s₁₀.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega_using []) (by omega_using []) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_using []) (by omega_using []) fC)
  obtain keep : ∀ d, 512 ≤ d → d + 4 ≤ 528 →
      s₁₀.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 => by
    rw [hm, sep _ _ d 532 (by omega_using [h2]) (by omega_using []) (by omega_using [h2]), sep _ _ d 528 (by omega_using [h2]) (by omega_using []) (by omega_using [h2]),
      hm₁, hp.scr_st _ (by omega_using [h2]) (by omega_using [hr₁, hj])]
  -- The registers.
  obtain g : ∀ r, r ∉ [Reg.ecx, .eax, .esi, .edi] → s₁₀.gpr r = s.gpr r := fun r hr => by
    have ⟨a, c', d, e⟩ : r ≠ .ecx ∧ r ≠ .eax ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₁₀.other r e, u₉.other r d, u₈.gpr, u₇.gpr,
      u₆.other r a, u₅.gpr, u₄.other r c', u₃.other r c']
  refine ⟨⟨by omega_using [hc], ?_, ?_, by rw [g _ (by decide), hI.ebx], by rw [g _ (by decide), hI.ebp],
    by rw [g _ (by decide), hI.esp], ?_, ?_, ?_,
    hI.frame.trans ((hfs.mono (by simp)).trans (hfc.mono (by simp))), hI.saved.keep keep⟩, ?_, ?_,
    by rw [g _ (by decide), d₂], ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hI.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, w₆]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr,
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      hI.esi, ofNat_add_one]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.gpr,
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      hI.edi, VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega_using [hc]), Nat.sub_sub]
  · rw [show rOff = 532 from rfl, hm, Mem.readW_writeW_self32]
  · rw [show pOff = 528 from rfl, hm, sep _ _ 528 532 (by omega_using []) (by omega_using []) (by omega_using []),
      Mem.readW_writeW_self32]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, e₆]
  · rw [show stateAt s₁₀.mem (stA s₀) = stateAt s₅.mem (stA s₀) from
      Proof.Sha3.stateAt_congr fun i hi => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi,
      bytesAt_one, xorAt_single]
    refine stateAt_xorByte (by omega_using [hr₁, hj]) ?_ fun i hi hij => ?_
    · rw [hm₁, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₁, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_using [hr₁, hj]) hij))]

theorem word_eq : absorbWord ++ storeVars8 ++ step8 =
    [.movqLoad .xmm0 (at_ .esi 0), .movqLoad .xmm1 (at_ .ecx 0), .xop (.bin .pxor .xmm0 .xmm1),
      .movqStore (at_ .ecx 0) .xmm0, .alu .add .ecx (.imm 8), .store (at_ .ebp 528) .ecx,
      .store (at_ .ebp 532) .edx, .alu .add .esi (.imm 8), .alu .sub .edi (.imm 8)] := rfl

/-- A turn of eight bytes: the eight bytes of data XORed into the state at
the position. -/
theorem word_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State} (hR : Ready s₀ c s)
    (hfit : (pos s₀ + c) % rt s₀ + 8 ≤ rt s₀) :
    WP isa (.block (absorbWord ++ storeVars8 ++ step8)) s (Turned s₀ c 8 ((pos s₀ + c) % rt s₀) s) := by
  have hI := hR.toInv
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain fS := hp.st_fit; have fC := hp.scr_fit; have fD := hp.d_fit
  obtain sep := fun (m : Mem) (v : BitVec 32) (d e : Nat) (hd : d + 4 ≤ 640) (he : e + 4 ≤ 640)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) => word_sep (b := scr s₀) (N := 640) fC hd he h m v
  obtain e₂ := hR.ecx
  obtain d₂ := hR.edx
  generalize (pos s₀ + c) % rt s₀ = j at hfit e₂ ⊢
  rw [word_eq]
  obtain hdA : addr (dp s₀ + BitVec.ofNat 32 c) 0 = dA s₀ + BitVec.ofNat 64 c := ptr_addr (by omega_using [hc, fD])
  obtain hsA : addr (st s₀ + BitVec.ofNat 32 j) 0 = stA s₀ + BitVec.ofNat 64 j := ptr_addr (by omega_using [hr₁, fS, hfit])
  refine wp_xor8 (a := dA s₀ + BitVec.ofNat 64 c) (b := stA s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [ea_at, hI.esi, hdA]) (by rw [ea_at, e₂, hsA])
    ⟨dR s₀, by simp [hI.rd, hp.rd], contains_offset (by omega_using [hc]) (by omega_using [hc, fD])⟩
    (by rw [hI.wr, hp.wr]; exact ⟨stR s₀, by simp, contains_offset (by omega_using [hr₁, hfit]) (by omega_using [hr₁, hfit])⟩)
    fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  obtain e₆ : s₆.gpr .ecx = st s₀ + BitVec.ofNat 32 (j + 8) := by
    rw [u₆.gpr, u₅.gpr, e₂]; exact ofNat_add_ofNat _ _ 8
  obtain hb₆ : s₆.gpr .ebp = scr s₀ := by rw [u₆.other _ (by decide), u₅.gpr, hI.ebp]
  obtain w₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, hI.wr]
  refine wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hb₆]) (hp.scr_out w₆ (by omega_using [])) fun s₇ u₇ => ?_
  refine wp_store (a := addr (scr s₀) 532) (by rw [ea_at, u₇.gpr, hb₆])
    (hp.scr_out (by rw [u₇.wr, w₆]) (by omega_using [])) fun s₈ u₈ => ?_
  refine wp_addi fun s₉ u₉ => wp_subi fun s₁₀ u₁₀ _ => WP.block_nil ?_
  -- The memory.
  obtain hm₁ := u₅.mem
  obtain hm : s₁₀.mem = (s₅.mem.writeW (addr (scr s₀) 528) (st s₀ + BitVec.ofNat 32 (j + 8))).writeW
      (addr (scr s₀) 532) (arg s₀ 1) := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.gpr, u₆.other _ (by decide), u₅.gpr, d₂, u₇.mem, u₆.mem, e₆]
  obtain hfs : Frame [stR s₀] s.mem s₅.mem := by
    rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_offset (by omega_using [hr₁, hfit]) (by omega_using [hr₁, hfit]))
  obtain hfc : Frame [scR s₀] s₅.mem s₁₀.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_addr (by omega_using []) (by omega_using []) fC)).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_using []) (by omega_using []) fC)
  obtain keep : ∀ d, 512 ≤ d → d + 4 ≤ 528 →
      s₁₀.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := fun d h1 h2 => by
    rw [hm, sep _ _ d 532 (by omega_using [h2]) (by omega_using []) (by omega_using [h2]), sep _ _ d 528 (by omega_using [h2]) (by omega_using []) (by omega_using [h2])]
    exact hfs.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact hp.st_scr.symm.sub_left (sub_word fC (by omega_using [h2]))) (by decide)
  -- The registers.
  obtain g : ∀ r, r ∉ [Reg.ecx, .esi, .edi] → s₁₀.gpr r = s.gpr r := fun r hr => by
    have ⟨a, d, e⟩ : r ≠ .ecx ∧ r ≠ .esi ∧ r ≠ .edi := by simpa using hr
    rw [u₁₀.other r e, u₉.other r d, u₈.gpr, u₇.gpr, u₆.other r a, u₅.gpr]
  refine ⟨⟨by omega_using [hc], ?_, ?_, by rw [g _ (by decide), hI.ebx], by rw [g _ (by decide), hI.ebp],
    by rw [g _ (by decide), hI.esp], ?_, ?_, ?_,
    hI.frame.trans ((hfs.mono (by simp)).trans (hfc.mono (by simp))), hI.saved.keep keep⟩, ?_, ?_,
    by rw [g _ (by decide), d₂], ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, hI.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, w₆]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.gpr, hI.esi]
    exact ofNat_add_ofNat _ _ 8
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.gpr, hI.edi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      VG.Proof.Sha256.X86.Stream.sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · rw [show rOff = 532 from rfl, hm, Mem.readW_writeW_self32]
  · rw [show pOff = 528 from rfl, hm, sep _ _ 528 532 (by omega_using []) (by omega_using []) (by omega_using []),
      Mem.readW_writeW_self32]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, e₆]
  · rw [show stateAt s₁₀.mem (stA s₀) = stateAt s₅.mem (stA s₀) from
      Proof.Sha3.stateAt_congr fun i hi => hfc.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi,
      hm₁]
    refine stateAt_write_word (by omega_using [hr₁, hfit]) (bytesAt_length _ _ _) fun d hd => ?_
    rw [BitVec.extractLsb'_xor, readW64_byte _ _ hd, readW64_byte _ _ hd, bytesAt_getD _ _ hd,
      BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (show c + d < len s₀ by omega_using [hc, hd]),
      BitVec.add_assoc, ← BitVec.ofNat_add]
    exact BitVec.xor_comm _ _

/-- A turn: of eight bytes where the block and the data have eight left, of
one byte otherwise. -/
theorem turn_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hR : Ready s₀ c s) :
    WP isa (turn (absorbByte ++ storeVars ++ step) (absorbWord ++ storeVars8 ++ step8)) s fun s' =>
      ∃ n, 0 < n ∧ c + n ≤ len s₀ ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
        Turned s₀ c n ((pos s₀ + c) % rt s₀) s s' := by
  have ⟨hr₀, _⟩ := hp.rt_pos
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain turned : ∀ {n j : Nat} {t s' : State}, t.mem = s.mem → Turned s₀ c n j t s' → Turned s₀ c n j s s' :=
    fun hm h => { h with state := by rw [← hm]; exact h.state }
  unfold turn
  refine WP.seq (WP.mono (room_ok hp hR) fun s₁ ⟨hR₁, hm₁, hc₁⟩ => ?_)
  refine WP.ite (decide (rt s₀ < (pos s₀ + c) % rt s₀ + 8)) (by rw [show isa.eval .b s₁ = s₁.cf from rfl, hc₁])
    (fun _ => WP.mono (byte_ok hp hc hR₁) fun s' h => ⟨1, by decide, hc, hj, turned hm₁ h⟩) (fun hb => ?_)
  simp only [decide_eq_false_iff_not] at hb
  refine WP.seq (WP.mono (left_ok hR₁) fun s₂ ⟨hR₂, hm₂', hc₂⟩ => ?_)
  obtain hm₂ : s₂.mem = s.mem := hm₂'.trans hm₁
  refine WP.ite (decide (len s₀ - c < 8)) (by rw [show isa.eval .b s₂ = s₂.cf from rfl, hc₂])
    (fun _ => WP.mono (byte_ok hp hc hR₂) fun s' h => ⟨1, by decide, hc, hj, turned hm₂ h⟩) (fun hb' => ?_)
  simp only [decide_eq_false_iff_not] at hb'
  exact WP.mono (word_ok hp (by omega_using [hb']) hR₂ (by omega_using [hb])) fun s' h =>
    ⟨8, by decide, by omega_using [hb'], by omega_using [hb], turned hm₂ h⟩

/-- The test for the end of the block. -/
theorem atEnd_ok {s₀ : State} (hp : Pre s₀) {c n j : Nat} {s s₁ : State} (hT : Turned s₀ c n j s s₁)
    (hfit : j + n ≤ rt s₀) :
    WP isa (.block atEnd) s₁ fun s' => Turned s₀ c n j s s' ∧ s'.zf = some (decide (j + n = rt s₀)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  refine wp_mov fun s₂ u₂ => wp_sub fun s₃ u₃ _ => wp_cmp fun s₄ u₄ _ z₄ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .eax → s₄.gpr r = s₁.gpr r := fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr]
  obtain hm : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
  obtain hax : s₃.gpr .eax = BitVec.ofNat 32 (j + n) := by
    rw [u₃.gpr, u₂.gpr, u₂.other .ebx (by decide), hT.ecx, hT.ebx, add_sub_self]
  obtain hdx : s₃.gpr .edx = BitVec.ofNat 32 (rt s₀) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), hT.edx]
    simp [rt]
  refine ⟨{
    c_le := hT.c_le
    rd := by rw [u₄.rd, u₃.rd, u₂.rd, hT.rd]
    wr := by rw [u₄.wr, u₃.wr, u₂.wr, hT.wr]
    ebx := by rw [g _ (by decide), hT.ebx]
    ebp := by rw [g _ (by decide), hT.ebp]
    esp := by rw [g _ (by decide), hT.esp]
    esi := by rw [g _ (by decide), hT.esi]
    edi := by rw [g _ (by decide), hT.edi]
    rate := by rw [hm]; exact hT.rate
    frame := by rw [hm]; exact hT.frame
    saved := by rw [hm]; exact hT.saved
    ptr := by rw [hm]; exact hT.ptr
    ecx := by rw [g _ (by decide), hT.ecx]
    edx := by rw [g _ (by decide), hT.edx]
    state := by rw [hm]; exact hT.state }, ?_⟩
  rw [z₄, hax, hdx, VG.Proof.Sha256.X86.Stream.sub_beq (by omega_using [hr₁, hfit]) (by omega_using [hr₁])]

/-- A store of the position keeps what holds throughout. -/
theorem Common.write_ptr {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    {v : BitVec 32} (u : Mupd s s' (s.mem.writeW (addr (scr s₀) 528) v)) : Common s₀ c s' where
  c_le := h.c_le
  rd := u.rd.trans h.rd
  wr := u.wr.trans h.wr
  ebx := by rw [u.gpr]; exact h.ebx
  ebp := by rw [u.gpr]; exact h.ebp
  esp := by rw [u.gpr]; exact h.esp
  esi := by rw [u.gpr]; exact h.esi
  edi := by rw [u.gpr]; exact h.edi
  rate := by
    rw [u.mem, show rOff = 532 from rfl, word_sep (N := 640) hp.scr_fit (by omega_using []) (by omega_using []) (by omega_using [])]
    exact h.rate
  frame := by rw [u.mem]; exact hp.frame_scr (by simp) h.frame (by omega_using []) _
  saved := h.saved.keep fun d h1 h2 => by
    rw [u.mem, word_sep (N := 640) hp.scr_fit (by omega_using [h2]) (by omega_using []) (by omega_using [h2])]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' =>
      (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
      (isa.eval .ne s' = some true ∧ ∃ n, 0 < n ∧ c + n < len s₀ ∧ Inv s₀ (c + n) s') := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (load_ok hp hI) fun s₀' hR => ?_)
  refine WP.seq (WP.mono (turn_ok hp hc hR) fun s₀'' ⟨n, hn, hcn, hfit, hT'⟩ => ?_)
  refine WP.seq (WP.mono (atEnd_ok hp hT' hfit) fun s₁ ⟨hT, hz⟩ => ?_)
  obtain hC := hT.toCommon
  obtain hptr := hT.ptr
  obtain hst := hT.state
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (stA s₀))
      else stateAt s₁.mem (stA s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_using [hr₁]) _ _
        (by rw [bytesAt_length]; exact hn) (by rw [hlen msg hm, bytesAt_length]; exact hfit),
      hlen msg hm, bytesAt_length, hst, hR.repr msg hm]
  obtain hpc := pos_add (p := pos s₀) (c := c) (n := n) hr₀ hfit
  -- The final test.
  obtain tail : ∀ t : State, Inv s₀ (c + n) t →
      WP isa (.block [.alu .test .edi (.reg .edi)]) t fun s' =>
        (isa.eval .ne s' = some false ∧ Inv s₀ (len s₀) s') ∨
        (isa.eval .ne s' = some true ∧ ∃ n, 0 < n ∧ c + n < len s₀ ∧ Inv s₀ (c + n) s') := by
    intro t ht
    refine wp_test fun s' u' z' => WP.block_nil ?_
    obtain ht' : Inv s₀ (c + n) s' :=
      { ht.toCommon.of_flags u' with
        ptr := by rw [u'.mem]; exact ht.ptr
        repr := by rw [u'.mem]; exact ht.repr }
    obtain hz : isa.eval .ne s' = some (!decide (len s₀ - (c + n) = 0)) := by
      simp only [eval, z', ht.edi, BitVec.and_self,
        VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (show len s₀ - (c + n) < 2 ^ 32 by omega_using [hl]), Option.map_some]
    by_cases he : c + n = len s₀
    · exact .inl ⟨by rw [hz]; simp [he], he ▸ ht'⟩
    · exact .inr ⟨by rw [hz]; simp; omega_using [hcn, he], n, hn, by omega_using [hcn, he], ht'⟩
  refine WP.seq (WP.mono (Q := Inv s₀ (c + n)) ?_ fun t ht => tail t ht)
  unfold next
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_store (a := addr (scr s₀) 528) (by rw [ea_at, hC.ebp]; rfl)
      (hp.scr_out hC.wr (by omega_using [])) fun s₂ u₂ => WP.block_nil ?_)
    obtain hC₂ := hC.write_ptr hp u₂
    have hwr := hC₂.wr
    refine permuteCall_ok (st := .ebx) (scr := .ebp) (by decide) (by decide) hC₂.esp hC₂.ebx hC₂.ebp
      hp.sp_lo hp.st_fit (by have := hp.scr_fit; omega_using [this])
      (hp.st_scr.sub_right (Region.sub_prefix (by omega_using []))) hp.stk_st
      (hp.stk_scr.sub_right (Region.sub_prefix (by omega_using []))) (by rw [hwr, hp.wr]; simp)
      (by rw [hwr, hp.wr]; simp) fun s₃ rd₃ wr₃ cs₃ f₃ e₃ => ?_
    refine { hC₂.after_call hp rd₃ wr₃ cs₃ f₃ with ptr := ?_, repr := fun msg hm => ?_ }
    · rw [show pOff = 528 from rfl, f₃.readW (r := ⟨addr (scr s₀) 528, 4⟩) (Region.contains_self _ _)
        (hp.hi_sep (d := 528) (by omega_using []) (by omega_using [])) (by decide), u₂.mem, Mem.readW_writeW_self32, hC.ebx,
        hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      simp
    · rw [e₃, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
      refine congrArg keccakF (Proof.Sha3.stateAt_congr fun i hi => ?_)
      obtain hf : Frame [scR s₀] s₁.mem s₂.mem := by
        rw [u₂.mem]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (contains_addr (by omega_using []) (by omega_using []) hp.scr_fit)
      exact hf.bytes (R := stR s₀) (by simpa using hp.st_scr) (by simp) hi
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC with ptr := ?_, repr := fun msg hm => ?_ }
    · rw [hptr, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

/-! ## The epilogue -/

theorem epilogue_eq : epilogue = .mov .eax (.mem (at_ .ebp 528)) :: .alu .sub .eax (.reg .ebx) ::
    .mov .ecx (.reg .ebp) :: (Spill.restoreCode .ecx saved ++ []) := rfl

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86.post s₀ s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  rw [epilogue_eq]
  refine wp_movm (a := addr (scr s₀) 528) (by rw [ea_at, hI.ebp]) (hp.scr_in hI.wr (by omega_using []))
    fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_mov fun s₃ u₃ => ?_
  obtain e₃ : s₃.gpr .ecx = scr s₀ := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.ebp]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr]
  obtain esp₃ : s₃.gpr .esp = s₀.gpr .esp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esp]
  refine Spill.restore_ok saved (by decide)
    (fun p h => by rw [e₃]; exact hp.scr_in w₃ (by have := saved_bound p h; omega_using [this]))
    (by rw [e₃, m₃]; exact hI.saved) fun s₇ r₇ =>
    WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, fun msg hm hpm => ?_, ?_⟩
  · exact r₇.abi (by decide) (by decide) esp₃ r hr
  · rw [r₇.mem, m₃]
    exact hI.frame.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk (E := E s₀) (by have := hp.sp_fit; omega_using [this]) hp.sp_lo⟩)
      (by decide)
  · rw [Proof.Sha3.repr_iff, r₇.mem, m₃]
    exact hI.repr msg ⟨hm, hpm⟩
  · have hptr : s.mem.readW (addr (scr s₀) 528) 32 = st s₀ + BitVec.ofNat 32 ((pos s₀ + len s₀) % rt s₀) :=
      hI.ptr
    rw [r₇.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hptr, hI.ebx, add_sub_self,
      VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_using [hr₁, this])]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbX86.post s₀ s' := by
  unfold absorb
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (len s₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
      ⟨0, rfl, by omega_using [hb], hI⟩
    rintro n s ⟨c, rfl, hc, hI⟩
    refine WP.mono (body_ok hp hc hI) fun s' h => ?_
    rcases h with ⟨he, hI'⟩ | ⟨he, m, hm, hc', hI'⟩
    · exact .inl ⟨he, hI'⟩
    · exact .inr ⟨he, len s₀ - (c + m), by omega_using [hc', hm], c + m, rfl, hc', hI'⟩

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and points `4` bytes below the
arguments (writable region 2), which are public; the words of `state` and
`scratch` are the base addresses of regions 0 and 1. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [200, 640, 24], bases := [(.esp, 2, 4)],
    slots := [(2, 0, 24)], wbases := [(2, 0, 0), (2, 20, 1)], room := 12 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  obtain hst := hp.st_fit; have hsc := hp.scr_fit
  have hs : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.sp_fit
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_scr, hp.a_st.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [addr_toNat]; omega_using [hst]
    · simp only [addr_toNat]; omega_using [hsc]
    · show (addr (s.gpr .esp) 4).toNat + 24 ≤ 2 ^ 32
      rw [addr_eq (by omega_using [hs]), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega_using [hs]
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 2).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 20) 32) 0 = (scr s).setWidth 64
      rw [argWord_eq (n := 24) (by omega_using [hs]) (k := 20) (by omega_using [])]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    obtain e : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 τ₀.room, τ₀.room⟩ : Region) = stkR s :=
      (stk_eq hlo).symm
    rw [e]
    rintro r (rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_scr
    · exact (arg_stk (n := 24) (by omega_using [hs]) hlo).symm

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.absorbX86.pre s₁) (h₂ : Proof.Sha3.absorbX86.pre s₂)
    (hpub : Proof.Sha3.absorbX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, argR, stA, st, scr, argAddr, ha 0 (by omega_using []), ha 5 (by omega_using []), hesp]
  · refine VG.X86.Taint.slotsOk_of_list rfl fun sl hsl => ?_
    simp only [List.mem_singleton] at hsl
    subst hsl; decide
  · intro i k hk
    rw [show τ₀.slots = VG.Slots.ofList [(2, 0, 24)] from rfl, VG.Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, _, hk⟩ := hk
    simp only [List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 24) (by have := hp₁.sp_fit; omega_using [this]) hk,
      argWord_eq (n := 24) (by have := hp₂.sp_fit; omega_using [this]) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

/-- Memory holding the arguments `0x1000, 72, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4008 then 72 else if a = 0x4011 then 0x20 else
  if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩, ⟨0x4004, 24⟩]

theorem sat_pre : Proof.Sha3.absorbX86.pre sat := by
  obtain a0 : arg sat 0 = 0x1000 := by decide
  obtain a1 : arg sat 1 = 72 := by decide
  obtain a2 : arg sat 2 = 0 := by decide
  obtain a3 : arg sat 3 = 0x2000 := by decide
  obtain a4 : arg sat 4 = 0 := by decide
  obtain a5 : arg sat 5 = 0x3000 := by decide
  obtain e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha3.absorbX86, a0, a1, a2, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩ <;>
  · exact Region.disjoint_of_sep (by decide)

theorem absorb_verified : Verified X86.target absorb Proof.Sha3.absorbX86 := by
  refine ⟨fun s hs => correct (pre_of hs), ?_, ⟨sat, sat_pre⟩⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide_weak VG.Proof.Sha3.X86.dropRC)

end VG.Proof.Sha3.X86.Stream.Absorb
