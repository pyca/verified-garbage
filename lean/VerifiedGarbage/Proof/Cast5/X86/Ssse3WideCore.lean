module

public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lookup
public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Cast5.Rotate
import VerifiedGarbage.Proof.Framework.CallLay

-- separate module: the sixteen-block function's proof, which the functions' checks (`Ssse3WideVerified.lean`) do not repeat

/-!
# CAST5's sixteen blocks by `pshufb` on x86 (32-bit): what the function computes

`vg_cast5_crypt_blocks16_ssse3` (`Impl.Cast5.X86.Ssse3.Wide.cryptBlocks`)
encrypts or decrypts the sixteen blocks at the start of its working space
(`cryptBlocks_wp`), and as the modes' core (`core16`) it meets what they
need of one (`coreSpec16`, `fits16`).

The working space is read at fixed offsets from `esi` (`Env16`), a
sixteen-byte place through the stores at the others (`Same`, `rd_wr`). The
halves of the blocks `4g` to `4g + 3` are the doublewords of two places
(`hv`): `blocksIn_wp` puts the blocks there (`decodeBlock`), and
`blocksOut_wp` back, exchanged (`encodeBlock`).

A round (`round_wp`), on the lanes of the registers (`Lanes.L`): its type
and subkeys from the round's number, which the working space holds
(`roundType_wp`, with `tyOf_eq` for the number modulo 3); `I` before its
rotation by the type (`mix_wp`), the code chosen by the branches on the type
(`byType_wp`); the rotation by `Kr`'s five bits (`rotate_wp`, the steps of
`Proof.Cast5.steps_eq`); the bytes of `I`, a register a byte (`planes_wp`);
an S-box's entries for the sixteen bytes (`sbox16_wp`: the index vectors
and the planes' rows of `Ssse3Lookup.lean`, `indexes_wp`, `scan_wp` and
`acc_entry`, then the bytes back to doublewords); `f` of the four entries by
the type and the other half (`combs_wp`, `comb_eq`); the next round's number
and the count (`next_wp`). The rounds are a loop on the count
(`wp_countdownF`) with the invariant `RInv`: after `i` rounds the halves are
`fold up k n i` of the blocks' (`fold_succ`, with `rnd_step` for the next
round's number), the block function's rounds after all `n`
(`VG.Proof.Cast5.X86.cipher_eq`).

`crypt_wp`: the core's `crypt`, which sets the first round's number, the
step (1, or -1 to decrypt) and the count from the mode's key arguments and
calls the function (`call_wp`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.Ssse3.Wide

open VG VG.X86 VG.X86.ByteLookup
open VG.Impl.Cast5.X86 (at_ imm)
open VG.Impl.Cast5.X86.Ssse3 (tb x ld stx xr index scan oC oT oM oKL oKR oBS oOnes oOne vOff tableName table tbr
  planeOff sboxOf)
open VG.Impl.Cast5.X86.Ssse3.Wide
open VG.X86.ByteMap (byte_eq_dword)
open VG.Spec.Cast5 (blockAt decodeBlock encodeBlock)

variable {s : State} {m : Mem}

/-! ## The working space's places -/

/-- A sixteen-byte place read through a store at another. -/
theorem rd_wr (m : Mem) (W : BitVec 32) {a b : Nat} (v : BitVec 128) (h : a + 16 ≤ b ∨ b + 16 ≤ a)
    (ha : a ≤ 4096) (hb : b ≤ 4096) : (m.writeW (slot W b) v).readW (slot W a) 128 = m.readW (slot W a) 128 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The sixteen-byte places from `lo` to `hi` hold in `m'` what they do in `m`. -/
def Same (W : BitVec 32) (lo hi : Nat) (m m' : Mem) : Prop :=
  ∀ o, lo ≤ o → o + 16 ≤ hi → m'.readW (slot W o) 128 = m.readW (slot W o) 128

theorem Same.refl (W : BitVec 32) (lo hi : Nat) (m : Mem) : Same W lo hi m m := fun _ _ _ => rfl

theorem Same.trans {W : BitVec 32} {lo hi : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Same W lo hi m₁ m₂)
    (h₂ : Same W lo hi m₂ m₃) : Same W lo hi m₁ m₃ := fun o a b => (h₂ o a b).trans (h₁ o a b)

theorem Same.mono {W : BitVec 32} {lo hi lo' hi' : Nat} {m₁ m₂ : Mem} (h : Same W lo hi m₁ m₂) (hl : lo ≤ lo')
    (hh : hi' ≤ hi) : Same W lo' hi' m₁ m₂ := fun o a b => h o (by omega) (by omega)

/-- A store at a place outside `lo` to `hi`. -/
theorem Same.write {W : BitVec 32} {lo hi : Nat} {m₁ m₂ : Mem} (h : Same W lo hi m₁ m₂) {b : Nat} (v : BitVec 128)
    (hb : b + 16 ≤ lo ∨ hi ≤ b) (hhi : hi ≤ 4096) (hb' : b ≤ 4096) : Same W lo hi m₁ (m₂.writeW (slot W b) v) :=
  fun o a c => (rd_wr m₂ W v (by omega) (by omega) hb').trans (h o a c)

/-- What changes only within `[a, a + n)` of the working space keeps the places outside it. -/
theorem Same.of_frame {W : BitVec 32} {lo hi a n : Nat} {m₁ m₂ : Mem} (h : Frame [⟨slot W a, n⟩] m₁ m₂)
    (hd : a + n ≤ lo ∨ hi ≤ a) (hhi : hi ≤ 4096) (ha : a + n ≤ 4096) : Same W lo hi m₁ m₂ := fun o c d =>
  h.readW (r := ⟨slot W o, 16⟩) (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)

/-! ## The state the function runs in -/

/-- Where the sixteen-block function runs: the working space at `W`, in
`esi`, its 848 bytes writable; the table's address in `edx`; the subkeys at
`K`, in `ebp`, readable. -/
structure Env16 (K W : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = W
  edx : s.gpr tbr = s.syms tableName
  ebp : s.gpr .ebp = K
  fW : W.toNat + 848 ≤ 2 ^ 32
  fK : K.toNat + 128 ≤ 2 ^ 32
  wrW : ∀ o n, o + n ≤ 848 → InRegions s.wr (slot W o) n
  rdK : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (slot K o) n

theorem Env16.env {K W : BitVec 32} (E : Env16 K W s) : Env W s :=
  ⟨E.esi, E.edx, by have := E.fW; omega, fun o n _ h' => E.wrW o n (by omega)⟩

theorem Env16.rdW {K W : BitVec 32} (E : Env16 K W s) {o n : Nat} (h' : o + n ≤ 848) :
    InRegions (s.rd ++ s.wr) (slot W o) n := by
  obtain ⟨r, hr, hc⟩ := E.wrW o n h'
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A load from the working space. -/
theorem wp_ldW {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {d : XReg} {o : Nat} (ho' : o + 16 ≤ 848)
    (k : WP isa (.block is) (S s m (upd f d (m.readW (slot W o) 128))) Q) :
    WP isa (.block (ld d .esi o :: is)) (S s m f) Q :=
  wp_ld (ea_at E.esi (by have := E.fW; omega)) (E.rdW ho') k

/-- A store to the working space. -/
theorem wp_stW {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {r : XReg} {o : Nat} (ho' : o + 16 ≤ 848)
    (k : WP isa (.block is) (S s (m.writeW (slot W o) (f r)) f) Q) :
    WP isa (.block (stx .esi o r :: is)) (S s m f) Q :=
  wp_st (ea_at E.esi (by have := E.fW; omega)) (E.wrW _ _ ho') k

/-- A constant. -/
theorem wp_tbE {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {d : XReg} {off : Nat} (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ 560)
    (k : WP isa (.block is) (S s m (upd f d (cst off))) Q) : WP isa (.block (tb d off :: is)) (S s m f) Q :=
  wp_tb E.edx ho k

/-! ## The transpositions -/

/-- The transposition of `xmm0` to `xmm3`: the rows in `xmm0`, `xmm6`, `xmm4` and `xmm7`. -/
theorem transpose0_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (k : ∀ g, g .xmm0 = tr (f .xmm0) (f .xmm1) (f .xmm2) (f .xmm3) 0 →
      g .xmm6 = tr (f .xmm0) (f .xmm1) (f .xmm2) (f .xmm3) 1 →
      g .xmm4 = tr (f .xmm0) (f .xmm1) (f .xmm2) (f .xmm3) 2 →
      g .xmm7 = tr (f .xmm0) (f .xmm1) (f .xmm2) (f .xmm3) 3 → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++ is)) (S s m f) Q :=
  wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin
    (k _ rfl rfl rfl rfl))))))))))))

/-- The transposition of `xmm4` to `xmm7`: the rows in `xmm4`, `xmm2`, `xmm0` and `xmm3`. -/
theorem transpose4_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (k : ∀ g, g .xmm4 = tr (f .xmm4) (f .xmm5) (f .xmm6) (f .xmm7) 0 →
      g .xmm2 = tr (f .xmm4) (f .xmm5) (f .xmm6) (f .xmm7) 1 →
      g .xmm0 = tr (f .xmm4) (f .xmm5) (f .xmm6) (f .xmm7) 2 →
      g .xmm3 = tr (f .xmm4) (f .xmm5) (f .xmm6) (f .xmm7) 3 → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm0 .xmm1 .xmm2 .xmm3 ++ is)) (S s m f) Q :=
  wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin
    (k _ rfl rfl rfl rfl))))))))))))

/-- The working space's bytes that the sixteen-block function writes. -/
abbrev wR16 (W : BitVec 32) : Region := ⟨W.setWidth 64, 848⟩

theorem wR16_contains (W : BitVec 32) {o : Nat} (h' : o + 16 ≤ 848) :
    (wR16 W).Contains (slot W o) (128 / 8) := Offset.contains_base _ h' (by omega)

/-! ## The blocks in -/

/-- The halves of block `b`, as the places of its group hold them. -/
def hv (m : Mem) (W : BitVec 32) (b : Nat) : BitVec 32 × BitVec 32 :=
  (dword (m.readW (slot W (lOff (b / 4))) 128) (b % 4), dword (m.readW (slot W (rOff (b / 4))) 128) (b % 4))

/-- The halves of block `b` of the buffer. -/
def st0 (m₀ : Mem) (W : BitVec 32) (b : Nat) : BitVec 32 × BitVec 32 :=
  decodeBlock (blockAt m₀ (slot W (bufOff + 8 * b)))

theorem cst_KL : ∀ c < 2, ∀ i < 4, byte (cst oKL) (4 * c + i) = BitVec.ofNat 8 (8 * c + 0 + 3 - i) := by lit_decide

theorem cst_KR : ∀ c < 2, ∀ i < 4, byte (cst oKR) (4 * c + i) = BitVec.ofNat 8 (8 * c + 4 + 3 - i) := by lit_decide

theorem cst_BS : ∀ d < 4, ∀ i < 4, byte (cst oBS) (4 * d + i) = BitVec.ofNat 8 (4 * d + 3 - i) := by lit_decide

theorem cst_Ones : ∀ k < 4, dword (cst oOnes) k = 0xFFFFFFFF#32 := by lit_decide

theorem cst_One : ∀ k < 4, dword (cst oOne) k = 1#32 := by lit_decide

theorem idx16 : ∀ n < 16, (BitVec.ofNat 8 n).msb = false ∧ ((BitVec.ofNat 8 n).extractLsb' 0 4).toNat = n := by
  decide

theorem shr8 (v : BitVec 32) (k : Nat) : (v >>> (8 * k)).setWidth 8 = v.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]

/-- Byte `i` of the halves of the block at `p`: the block's bytes are
big-endian. -/
theorem half_byte (m : Mem) (p : Addr) {i : Nat} (hi : i < 4) :
    (decodeBlock (blockAt m p)).1.extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 (0 + 3 - i)) ∧
      (decodeBlock (blockAt m p)).2.extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 (4 + 3 - i)) := by
  rw [Proof.Cast5.decodeBlock_blockAt]
  refine ⟨?_, ?_⟩
  · show (byteRev32 (m.readW p 32)).extractLsb' (8 * i) 8 = _
    rw [Proof.Cast5.byteRev32_byte _ hi, shr8, byte_readW m p (by omega), Nat.zero_add]
  · show (byteRev32 (m.readW (p + BitVec.ofNat 64 4) 32)).extractLsb' (8 * i) 8 = _
    rw [Proof.Cast5.byteRev32_byte _ hi, shr8, byte_readW m _ (by omega), Offset.add_add,
      show 4 + (3 - i) = 4 + 3 - i by omega]

/-- A byte of a half of one of the two blocks of sixteen bytes, by the
shuffle `Kc` whose bytes `4c + i` are `8c + o + 3 - i`. -/
theorem in_byte {m : Mem} {a : Addr} {Kc : BitVec 128} {o : Nat} (ho : o ≤ 4)
    (hK : ∀ c < 2, ∀ i < 4, byte Kc (4 * c + i) = BitVec.ofNat 8 (8 * c + o + 3 - i)) {c : Nat} (hc : c < 2)
    {i : Nat} (hi : i < 4) :
    (dword (XBinOp.eval .pshufb (m.readW a 128) Kc) c).extractLsb' (8 * i) 8 =
      m (a + BitVec.ofNat 64 (8 * c + o + 3 - i)) := by
  obtain ⟨e1, e2⟩ := idx16 (8 * c + o + 3 - i) (by omega)
  rw [byte_of_dword _ _ hi, ByteMap.byte_pshufb _ _ (by omega), hK c hc i hi, e1, e2, ite_eq_right Bool.false_ne_true]
  exact byte_readW m a (by omega)

/-- A byte of a half of block `4g + k` of the buffer, in doubleword `k` of
the group's register. -/
theorem in_lane {m₀ : Mem} {W : BitVec 32} {Kc : BitVec 128} {o : Nat} (ho : o ≤ 4)
    (hK : ∀ c < 2, ∀ i < 4, byte Kc (4 * c + i) = BitVec.ofNat 8 (8 * c + o + 3 - i)) {g k : Nat} (hk : k < 4)
    {i : Nat} (hi : i < 4) :
    (dword (XBinOp.eval .punpcklqdq (XBinOp.eval .pshufb (m₀.readW (slot W (bufOff + 32 * g)) 128) Kc)
      (XBinOp.eval .pshufb (m₀.readW (slot W (bufOff + 32 * g + 16)) 128) Kc)) k).extractLsb' (8 * i) 8 =
      m₀ (slot W (bufOff + 8 * (4 * g + k)) + BitVec.ofNat 64 (o + 3 - i)) := by
  rw [punpcklqdq_eq]
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · rw [dword_ofDwords_0, in_byte ho hK (c := 0) (by decide) hi, Offset.add_add, Offset.add_add]
    exact congrArg m₀ (congrArg (fun n => W.setWidth 64 + BitVec.ofNat 64 n) (by omega))
  · rw [dword_ofDwords_1, in_byte ho hK (c := 1) (by decide) hi, Offset.add_add, Offset.add_add]
    exact congrArg m₀ (congrArg (fun n => W.setWidth 64 + BitVec.ofNat 64 n) (by omega))
  · rw [dword_ofDwords_2, in_byte ho hK (c := 0) (by decide) hi, Offset.add_add, Offset.add_add]
    exact congrArg m₀ (congrArg (fun n => W.setWidth 64 + BitVec.ofNat 64 n) (by omega))
  · rw [dword_ofDwords_3, in_byte ho hK (c := 1) (by decide) hi, Offset.add_add, Offset.add_add]
    exact congrArg m₀ (congrArg (fun n => W.setWidth 64 + BitVec.ofNat 64 n) (by omega))

/-- The halves of the blocks `4g` to `4g + 3`, to their places. -/
theorem blockIn_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {g : Nat} (hg : g < 4)
    (k : ∀ f', f' .xmm6 = f .xmm6 → f' .xmm7 = f .xmm7 →
      WP isa (.block is) (S s ((m.writeW (slot W (lOff g)) (XBinOp.eval .punpcklqdq
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g)) 128) (f .xmm6))
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g + 16)) 128) (f .xmm6)))).writeW (slot W (rOff g))
        (XBinOp.eval .punpcklqdq (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g)) 128) (f .xmm7))
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g + 16)) 128) (f .xmm7)))) f') Q) :
    WP isa (.block (blockIn g ++ is)) (S s m f) Q :=
  wp_ldW E (by simp only [bufOff]; omega) (wp_ldW E (by simp only [bufOff]; omega)
    (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_stW E
    (by simp only [lOff]; omega) (wp_stW E (by simp only [rOff]; omega) (k _ rfl rfl))))))))))))

/-- The halves of the groups `g` to `g + n - 1`, to their places. -/
theorem blocksIn_wp {K W : BitVec 32} (E : Env16 K W s) {is : List Instr} {Q : State → Prop} {m₀ : Mem}
    (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 → f .xmm6 = cst oKL → f .xmm7 = cst oKR →
      (∀ b < 4 * g, hv m W b = st0 m₀ W b) → Same W 0 128 m₀ m → Same W 256 848 m₀ m → Frame [wR16 W] m₀ m →
      (∀ m' f', (∀ b < 4 * (g + n), hv m' W b = st0 m₀ W b) → Same W 256 848 m₀ m' → Frame [wR16 W] m₀ m' →
        WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap blockIn ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ hh _ hs' hf k => k m f hh hs' hf
  | succ n ih =>
    intro g m f hn h6 h7 hh hs hs' hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine blockIn_wp E (by omega) fun f' e6 e7 => ?_
    rw [h6, h7, hs _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega),
      hs _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)]
    refine ih (g + 1) _ f' (by omega) (e6.trans h6) (e7.trans h7) (fun b hb => ?_)
      ((hs.write _ (.inr (by simp only [lOff]; omega)) (by decide) (by simp only [lOff]; omega)).write _
        (.inr (by simp only [rOff]; omega)) (by decide) (by simp only [rOff]; omega))
      ((hs'.write _ (.inl (by simp only [lOff]; omega)) (by decide) (by simp only [lOff]; omega)).write _
        (.inl (by simp only [rOff]; omega)) (by decide) (by simp only [rOff]; omega))
      ((hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [lOff]; omega))).writeW List.mem_cons_self _
        (wR16_contains W (by simp only [rOff]; omega)))
      fun m' f'' hh' hs'' hf' => k m' f'' (fun b hb => hh' b (by omega)) hs'' hf'
    by_cases hb' : b < 4 * g
    · rw [← hh b hb']
      refine Prod.ext ?_ ?_
      · show dword (Mem.readW _ (slot W (lOff (b / 4))) 128) (b % 4) = dword (m.readW (slot W (lOff (b / 4))) 128) (b % 4)
        rw [rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [lOff]; omega) (by simp only [rOff]; omega),
          rd_wr _ W _ (by simp only [lOff]; omega) (by simp only [lOff]; omega) (by simp only [lOff]; omega)]
      · show dword (Mem.readW _ (slot W (rOff (b / 4))) 128) (b % 4) = dword (m.readW (slot W (rOff (b / 4))) 128) (b % 4)
        rw [rd_wr _ W _ (by simp only [rOff]; omega) (by simp only [rOff]; omega) (by simp only [rOff]; omega),
          rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [rOff]; omega) (by simp only [lOff]; omega)]
    · obtain eg : b / 4 = g := by omega
      refine Prod.ext (word_ext fun i hi => ?_) (word_ext fun i hi => ?_)
      · show (dword (Mem.readW _ (slot W (lOff (b / 4))) 128) (b % 4)).extractLsb' (8 * i) 8 = _
        rw [eg, rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [lOff]; omega)
          (by simp only [rOff]; omega), readW_self128, in_lane (o := 0) (by decide) cst_KL (Nat.mod_lt _ (by decide)) hi,
          show 4 * g + b % 4 = b by omega]
        exact ((half_byte m₀ _ hi).1).symm
      · show (dword (Mem.readW _ (slot W (rOff (b / 4))) 128) (b % 4)).extractLsb' (8 * i) 8 = _
        rw [eg, readW_self128, in_lane (o := 4) (by decide) cst_KR (Nat.mod_lt _ (by decide)) hi,
          show 4 * g + b % 4 = b by omega]
        exact ((half_byte m₀ _ hi).2).symm

/-! ## The blocks out -/

/-- Two doublewords of a register stored through the shuffle that reverses
each doubleword's bytes: a block of their big-endian bytes. -/
theorem out_half {m : Mem} {a : Addr} {v : BitVec 128} (h : m.readW a 128 = XBinOp.eval .pshufb v (cst oBS)) {d : Nat}
    (hd : d + 1 < 4) : blockAt m (a + BitVec.ofNat 64 (4 * d)) = encodeBlock (dword v d, dword v (d + 1)) := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Offset.add_add, ← byte_readW m a (w := 128) (k := 4 * d + j) (by omega), h]
  simp only [encodeBlock, Vector.getElem_ofFn]
  show byte (XBinOp.eval .pshufb v (cst oBS)) (4 * d + j) = _
  by_cases h4 : j < 4
  · obtain ⟨e1, e2⟩ := idx16 (4 * d + 3 - j) (by omega)
    rw [ite_eq_left h4, ByteMap.byte_pshufb _ _ (by omega), cst_BS d (by omega) j h4, e1, e2,
      ite_eq_right Bool.false_ne_true, Nat.mod_eq_of_lt h4, shr8, byte_of_dword _ _ (by omega),
      show 4 * d + (3 - j) = 4 * d + 3 - j by omega]
  · obtain ⟨e1, e2⟩ := idx16 (4 * (d + 1) + 3 - (j - 4)) (by omega)
    rw [ite_eq_right h4, show 4 * d + j = 4 * (d + 1) + (j - 4) by omega, ByteMap.byte_pshufb _ _ (by omega),
      cst_BS (d + 1) (by omega) (j - 4) (by omega), e1, e2, ite_eq_right Bool.false_ne_true,
      show j % 4 = j - 4 by omega, shr8, byte_of_dword _ _ (by omega),
      show 4 * (d + 1) + (3 - (j - 4)) = 4 * (d + 1) + 3 - (j - 4) by omega]

/-- Block `4g + k` of the buffer, from doubleword `k` of the group's two registers. -/
theorem out_lanes {m : Mem} {W : BitVec 32} {A B : BitVec 128} {g : Nat}
    (h0 : m.readW (slot W (bufOff + 32 * g)) 128 = XBinOp.eval .pshufb (XBinOp.eval .punpckldq A B) (cst oBS))
    (h1 : m.readW (slot W (bufOff + 32 * g + 16)) 128 = XBinOp.eval .pshufb (XBinOp.eval .punpckhdq A B) (cst oBS))
    {k : Nat} (hk : k < 4) :
    blockAt m (slot W (bufOff + 8 * (4 * g + k))) = encodeBlock (dword A k, dword B k) := by
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · have h := out_half h0 (d := 0) (by decide)
    rw [Offset.add_add, punpckldq_eq] at h
    simp only [Nat.reduceAdd, Nat.reduceMul, dword_ofDwords_0, dword_ofDwords_1] at h
    rw [show bufOff + 8 * (4 * g + 0) = bufOff + 32 * g + 0 by omega]; exact h
  · have h := out_half h0 (d := 2) (by decide)
    rw [Offset.add_add, punpckldq_eq] at h
    simp only [Nat.reduceAdd, Nat.reduceMul, dword_ofDwords_2, dword_ofDwords_3] at h
    rw [show bufOff + 8 * (4 * g + 1) = bufOff + 32 * g + 8 by omega]; exact h
  · have h := out_half h1 (d := 0) (by decide)
    rw [Offset.add_add, punpckhdq_eq] at h
    simp only [Nat.reduceAdd, Nat.reduceMul, dword_ofDwords_0, dword_ofDwords_1] at h
    rw [show bufOff + 8 * (4 * g + 2) = bufOff + 32 * g + 16 + 0 by omega]; exact h
  · have h := out_half h1 (d := 2) (by decide)
    rw [Offset.add_add, punpckhdq_eq] at h
    simp only [Nat.reduceAdd, Nat.reduceMul, dword_ofDwords_2, dword_ofDwords_3] at h
    rw [show bufOff + 8 * (4 * g + 3) = bufOff + 32 * g + 16 + 8 by omega]; exact h

/-- The first two blocks of a group as they are stored: `R` and `L`, a
block's two doublewords together, their bytes reversed. -/
abbrev oL (r l bs : BitVec 128) : BitVec 128 := XBinOp.eval .pshufb (XBinOp.eval .punpckldq r l) bs

/-- The last two blocks of a group. -/
abbrev oH (r l bs : BitVec 128) : BitVec 128 := XBinOp.eval .pshufb (XBinOp.eval .punpckhdq r l) bs

/-- The blocks `4g` to `4g + 3`, from their halves to the buffer. -/
theorem blockOut_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {g : Nat} (hg : g < 4)
    (k : ∀ f', f' .xmm5 = f .xmm5 →
      WP isa (.block is) (S s ((m.writeW (slot W (bufOff + 32 * g)) (oL (m.readW (slot W (rOff g)) 128)
          (m.readW (slot W (lOff g)) 128) (f .xmm5))).writeW (slot W (bufOff + 32 * g + 16))
        (oH (m.readW (slot W (rOff g)) 128) (m.readW (slot W (lOff g)) 128) (f .xmm5))) f') Q) :
    WP isa (.block (blockOut g ++ is)) (S s m f) Q :=
  wp_ldW E (by simp only [rOff]; omega) (wp_ldW E (by simp only [lOff]; omega) (wp_bin (wp_bin (wp_bin (wp_bin
    (wp_bin (wp_stW E (by simp only [bufOff]; omega) (wp_stW E (by simp only [bufOff]; omega) (k _ rfl)))))))))

/-- The blocks of the groups `g` to `g + n - 1`, to the buffer. -/
theorem blockOuts_wp {K W : BitVec 32} (E : Env16 K W s) {is : List Instr} {Q : State → Prop} {m₀ : Mem}
    (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 → f .xmm5 = cst oBS →
      (∀ g' < g, m.readW (slot W (bufOff + 32 * g')) 128 = oL (m₀.readW (slot W (rOff g')) 128)
          (m₀.readW (slot W (lOff g')) 128) (cst oBS) ∧
        m.readW (slot W (bufOff + 32 * g' + 16)) 128 = oH (m₀.readW (slot W (rOff g')) 128)
          (m₀.readW (slot W (lOff g')) 128) (cst oBS)) →
      Same W 128 256 m₀ m → Frame [wR16 W] m₀ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (bufOff + 32 * g')) 128 = oL (m₀.readW (slot W (rOff g')) 128)
          (m₀.readW (slot W (lOff g')) 128) (cst oBS) ∧
        m'.readW (slot W (bufOff + 32 * g' + 16)) 128 = oH (m₀.readW (slot W (rOff g')) 128)
          (m₀.readW (slot W (lOff g')) 128) (cst oBS)) → Frame [wR16 W] m₀ m' →
        WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap blockOut ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ hh _ hf k => k m f hh hf
  | succ n ih =>
    intro g m f hn h5 hh hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine blockOut_wp E (by omega) fun f' e5 => ?_
    rw [h5, hs (rOff g) (by simp only [rOff]; omega) (by simp only [rOff]; omega),
      hs (lOff g) (by simp only [lOff]; omega) (by simp only [lOff]; omega)]
    refine ih (g + 1) _ f' (by omega) (e5.trans h5) (fun g' hg' => ?_)
      ((hs.write _ (.inl (by simp only [bufOff]; omega)) (by decide) (by simp only [bufOff]; omega)).write _
        (.inl (by simp only [bufOff]; omega)) (by decide) (by simp only [bufOff]; omega))
      ((hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [bufOff]; omega))).writeW List.mem_cons_self _
        (wR16_contains W (by simp only [bufOff]; omega)))
      fun m' f'' hh' hf' => k m' f'' (fun g' hg' => hh' g' (by omega)) hf'
    by_cases e : g' = g
    · rw [e]
      exact ⟨(rd_wr _ W _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
        (by simp only [bufOff]; omega)).trans (readW_self128 _ _ _), readW_self128 _ _ _⟩
    · obtain ⟨a, b⟩ := hh g' (by omega)
      exact ⟨(rd_wr _ W _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
          (by simp only [bufOff]; omega)).trans ((rd_wr _ W _ (by simp only [bufOff]; omega)
          (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)).trans a),
        (rd_wr _ W _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
          (by simp only [bufOff]; omega)).trans ((rd_wr _ W _ (by simp only [bufOff]; omega)
          (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)).trans b)⟩

/-- **The sixteen blocks out**: the halves after the last round, `R` first,
as the blocks of the buffer. -/
theorem blocksOut_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {Q : State → Prop}
    (k : ∀ m' g, (∀ b < 16, blockAt m' (slot W (bufOff + 8 * b)) = encodeBlock ((hv m W b).2, (hv m W b).1)) →
      Frame [wR16 W] m m' → Q (S s m' g)) :
    WP isa (.block blocksOut) (S s m f) Q := by
  rw [show blocksOut = tb .xmm5 oBS :: ((List.range' 0 4).flatMap blockOut ++ []) by
    rw [blocksOut, List.range_eq_range', List.append_nil]; rfl]
  refine wp_tbE E (by decide) (blockOuts_wp E (m₀ := m) 4 0 m _ (by decide) rfl
    (fun g' h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Frame.refl _ _) fun m' f' hh hf =>
    WP.block_nil (k m' f' (fun b hb => ?_) hf))
  obtain ⟨h0, h1⟩ := hh (b / 4) (by omega)
  have h := out_lanes h0 h1 (k := b % 4) (Nat.mod_lt _ (by decide))
  rw [show 4 * (b / 4) + b % 4 = b by omega] at h
  exact h

/-! ## Lanes, and the general registers among the XMM instructions -/

open VG.X86.Lanes (L dword_L L_ext L_dword L_congr por_L pxor_L pand_L bcast_L)
open VG.X86.Wp

theorem pslld_Ln (f : Nat → BitVec 32) (n : BitVec 8) (hn : n.toNat < 32) :
    XShiftOp.eval .pslld (L f) n = L fun k => f k <<< n.toNat :=
  L_ext fun k hk => by rw [dword_pslld _ _ hn hk, dword_L _ hk]

theorem psrld_Ln (f : Nat → BitVec 32) (n : BitVec 8) (hn : n.toNat < 32) :
    XShiftOp.eval .psrld (L f) n = L fun k => f k >>> n.toNat :=
  L_ext fun k hk => by rw [dword_psrld _ _ hn hk, dword_L _ hk]

/-- What the round's code on the XMM registers keeps of a state. -/
structure Stay (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms

theorem Stay.refl (s : State) : Stay s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Stay.trans {s₁ s₂ s₃ : State} (h : Stay s₁ s₂) (h' : Stay s₂ s₃) : Stay s₁ s₃ :=
  ⟨fun r a b => (h'.gpr r a b).trans (h.gpr r a b), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.syms.trans h.syms⟩

theorem Stay.S (s : State) (m : Mem) (f : XReg → BitVec 128) : Stay s (S s m f) := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Stay.upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) (hd : d = .eax ∨ d = .ecx) :
    Stay s s' :=
  ⟨fun r a b => u.other r (by rcases hd with rfl | rfl <;> with_reducible assumption), u.rd, u.wr, u.syms⟩

theorem Env16.stay {K W : BitVec 32} {s s' : State} (E : Env16 K W s) (h : Stay s s') : Env16 K W s' :=
  ⟨(h.gpr _ (by decide) (by decide)).trans E.esi,
    ((h.gpr _ (by decide) (by decide)).trans E.edx).trans (by rw [h.syms]),
    (h.gpr _ (by decide) (by decide)).trans E.ebp, E.fW, E.fK, by rw [h.wr]; exact E.wrW,
    by rw [h.rd, h.wr]; exact E.rdK⟩

section
variable {is : List Instr} {Q : State → Prop}

theorem wp_movx {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q := Wp.cons rfl (k _ (Upd.setReg _ _ _) rfl)

theorem wp_andix {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q := Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_subix {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d - v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q := Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addix {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q := Wp.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_shrx {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  Wp.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1))) (if n = 1 then some (s.gpr d).msb else none)
      (some (s.gpr d >>> n == 0)) (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n))
    (by simp only [reduceExec, execShift, hn, and_self, ite_true]) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

theorem wp_cmpix {d : Reg} {v : BitVec 32}
    (k : ∀ s', Fupd s s' → s'.zf = some (s.gpr d - v == 0) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q := Wp.cons rfl (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

end

/-! ## The rotation -/

theorem xr_lt4_ne {g : Nat} (hg : g < 4) :
    xr g ≠ .xmm4 ∧ xr g ≠ .xmm5 ∧ xr g ≠ .xmm6 ∧ xr g ≠ .xmm7 := by
  rcases cases4 hg with rfl | rfl | rfl | rfl <;> decide

theorem rot_shifts {b : Nat} (hb : b < 5) :
    (BitVec.ofNat 8 (2 ^ b)).toNat = 2 ^ b ∧ (BitVec.ofNat 8 (32 - 2 ^ b)).toNat = 32 - 2 ^ b ∧ 0 < 2 ^ b ∧
      2 ^ b < 32 := by
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega) with h | h | h | h | h <;> subst h <;> decide

/-- Step `b` of the rotation of register `g`, on its lanes. -/
theorem rotG_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {b g : Nat} (hb : b < 5)
    (hg : g < 4) {v : Nat → BitVec 32} {kb : BitVec 32} (hx : f (xr g) = L v)
    (h6 : f .xmm6 = L fun _ => (kb &&& 1) - 1)
    (k : ∀ f', f' (xr g) = L (fun c => Proof.Cast5.step (v c) kb b) →
      (∀ q, q ≠ xr g → q ≠ .xmm4 → q ≠ .xmm5 → f' q = f q) → WP isa (.block is) (S s m f') Q) :
    WP isa (.block (rotG b g ++ is)) (S s m f) Q := by
  obtain ⟨n4, n5, n6, -⟩ := xr_lt4_ne hg
  obtain ⟨e1, e2, p0, p32⟩ := rot_shifts hb
  show WP isa (.block (x .movdqa .xmm4 (xr g) :: x .movdqa .xmm5 (xr g) ::
    .xop (.shift .pslld .xmm4 (BitVec.ofNat 8 (2 ^ b))) :: .xop (.shift .psrld .xmm5 (BitVec.ofNat 8 (32 - 2 ^ b))) ::
    x .por .xmm4 .xmm5 :: x .pxor (xr g) .xmm4 :: x .pand (xr g) .xmm6 :: x .pxor (xr g) .xmm4 :: is)) _ _
  refine wp_bin (wp_bin (wp_xs rfl (wp_xs rfl (wp_bin (wp_bin (wp_bin (wp_bin (k _ ?_ fun q a b c => ?_))))))))
  · simp only [upd_self, upd_ne _ _ n4, upd_ne _ _ n5, upd_ne _ _ n4.symm, upd_ne _ _ n6.symm,
      upd_ne _ _ (show (.xmm5 : XReg) ≠ .xmm4 by decide), upd_ne _ _ (show (.xmm4 : XReg) ≠ .xmm5 by decide),
      upd_ne _ _ (show (.xmm6 : XReg) ≠ .xmm4 by decide), upd_ne _ _ (show (.xmm6 : XReg) ≠ .xmm5 by decide),
      hx, h6, eval_movdqa]
    rw [pslld_Ln _ _ (by rw [e1]; exact p32), psrld_Ln _ _ (by rw [e2]; omega), por_L, pxor_L, pand_L, pxor_L, e1, e2]
    refine L_congr fun c _ => ?_
    show _ = ((v c ^^^ (v c).rotateRight (32 - 2 ^ b)) &&& ((kb &&& 1) - 1)) ^^^ (v c).rotateRight (32 - 2 ^ b)
    rw [Proof.Cast5.rotateRight_eq_rotateLeft _ p0 (Nat.le_of_lt p32), shl_or_shr _ p0 p32]
  · simp only [upd_ne _ _ a, upd_ne _ _ b, upd_ne _ _ c]

theorem range4 {α : Type} (f : Nat → List α) : (List.range 4).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ (f 3 ++ []))) := rfl

/-- Step `b` of the rotation of the four registers by the bits of `ecx`. -/
theorem rotStep_wp {s : State} {is : List Instr} {Q : State → Prop} {b : Nat}
    (hb : b < 5) {v : Nat → Nat → BitVec 32} {kb : BitVec 32} (hcx : s.gpr .ecx = kb)
    (hx : ∀ g < 4, s.xmm (xr g) = L (v g))
    (k : ∀ s', Stay s s' → s'.gpr .ecx = (if b < 4 then kb >>> 1 else kb) →
      (∀ g < 4, s'.xmm (xr g) = L fun c => Proof.Cast5.step (v g c) kb b) → s'.mem = s.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block (rotStep b ++ is)) s Q := by
  rw [rotStep, range4]
  show WP isa (.block (.mov .eax (.reg .ecx) :: .alu .and .eax (imm 1) :: .alu .sub .eax (imm 1) ::
    .xop (.movd .xmm6 .eax) :: .xop (.pshufd .xmm6 .xmm6 0) :: (rotG b 0 ++ (rotG b 1 ++ (rotG b 2 ++ (rotG b 3 ++
      ((if b < 4 then [.shift .shr .ecx 1] else []) ++ is))))))) s Q
  refine wp_movx fun s₁ u₁ x₁ => wp_andix fun s₂ u₂ x₂ => wp_subix fun s₃ u₃ x₃ => ?_
  obtain X : s₃.xmm = s.xmm := by rw [x₃, x₂, x₁]
  obtain M : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain ST : Stay s s₃ := ((Stay.upd u₁ (.inl rfl)).trans (Stay.upd u₂ (.inl rfl))).trans (Stay.upd u₃ (.inl rfl))
  obtain ax : s₃.gpr .eax = (kb &&& 1) - 1 := by rw [u₃.gpr, u₂.gpr, u₁.gpr, hcx]; rfl
  obtain cx : s₃.gpr .ecx = kb := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hcx]
  show WP isa _ (S s₃ s₃.mem s₃.xmm) _
  refine wp_xs rfl (wp_xs rfl ?_)
  show WP isa _ (S s₃ s₃.mem (upd (upd s₃.xmm .xmm6 ((0 : BitVec 96) ++ s₃.gpr .eax)) .xmm6
    (shufDwords ((0 : BitVec 96) ++ s₃.gpr .eax) 0))) _
  rw [ax, bcast_L]
  have x6 : ∀ g < 4, upd (upd s₃.xmm .xmm6 ((0 : BitVec 96) ++ ((kb &&& 1) - 1))) .xmm6
      (L fun _ => (kb &&& 1) - 1) (xr g) = L (v g) := fun g hg => by
    rw [upd_ne _ _ (xr_lt4_ne hg).2.2.1, upd_ne _ _ (xr_lt4_ne hg).2.2.1, X]; exact hx g hg
  have n01 : xr 1 ≠ xr 0 := by decide
  have n02 : xr 2 ≠ xr 0 := by decide
  have n03 : xr 3 ≠ xr 0 := by decide
  have n12 : xr 2 ≠ xr 1 := by decide
  have n13 : xr 3 ≠ xr 1 := by decide
  have n23 : xr 3 ≠ xr 2 := by decide
  have n6 : ∀ g < 4, (.xmm6 : XReg) ≠ xr g := fun g hg => (xr_lt4_ne hg).2.2.1.symm
  have n4 : ∀ g < 4, xr g ≠ .xmm4 := fun g hg => (xr_lt4_ne hg).1
  have n5 : ∀ g < 4, xr g ≠ .xmm5 := fun g hg => (xr_lt4_ne hg).2.1
  refine rotG_wp hb (by decide) (x6 0 (by decide)) (upd_self _ _ _) fun f1 a1 o1 =>
    rotG_wp hb (by decide) ((o1 _ n01 (n4 1 (by decide)) (n5 1 (by decide))).trans (x6 1 (by decide)))
      ((o1 _ (n6 0 (by decide)) (by decide) (by decide)).trans (upd_self _ _ _)) fun f2 a2 o2 =>
    rotG_wp hb (by decide)
      ((o2 _ n12 (n4 2 (by decide)) (n5 2 (by decide))).trans ((o1 _ n02 (n4 2 (by decide))
        (n5 2 (by decide))).trans (x6 2 (by decide))))
      ((o2 _ (n6 1 (by decide)) (by decide) (by decide)).trans ((o1 _ (n6 0 (by decide)) (by decide)
        (by decide)).trans (upd_self _ _ _))) fun f3 a3 o3 =>
    rotG_wp hb (by decide)
      ((o3 _ n23 (n4 3 (by decide)) (n5 3 (by decide))).trans ((o2 _ n13 (n4 3 (by decide))
        (n5 3 (by decide))).trans ((o1 _ n03 (n4 3 (by decide)) (n5 3 (by decide))).trans (x6 3 (by decide)))))
      ((o3 _ (n6 2 (by decide)) (by decide) (by decide)).trans ((o2 _ (n6 1 (by decide)) (by decide)
        (by decide)).trans ((o1 _ (n6 0 (by decide)) (by decide) (by decide)).trans (upd_self _ _ _))))
      fun f4 a4 o4 => ?_
  obtain R : ∀ g < 4, f4 (xr g) = L fun c => Proof.Cast5.step (v g c) kb b := fun g hg => by
    rcases cases4 hg with rfl | rfl | rfl | rfl
    · rw [o4 _ n03.symm (n4 0 (by decide)) (n5 0 (by decide)), o3 _ n02.symm (n4 0 (by decide)) (n5 0 (by decide)),
        o2 _ n01.symm (n4 0 (by decide)) (n5 0 (by decide))]; exact a1
    · rw [o4 _ n13.symm (n4 1 (by decide)) (n5 1 (by decide)), o3 _ n12.symm (n4 1 (by decide)) (n5 1 (by decide))]
      exact a2
    · rw [o4 _ n23.symm (n4 2 (by decide)) (n5 2 (by decide))]; exact a3
    · exact a4
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    refine wp_shrx (by decide) fun s₄ u₄ x₄ => k s₄ ((ST.trans (Stay.S s₃ _ _)).trans (Stay.upd u₄ (.inr rfl)))
      ?_ ?_ (u₄.mem.trans M)
    · rw [ite_eq_left h4, u₄.gpr]
      show s₃.gpr .ecx >>> 1 = kb >>> 1
      rw [cx]
    · intro g hg; rw [x₄]; exact R g hg
  · rw [ite_eq_right h4]
    exact k _ (ST.trans (Stay.S s₃ _ _)) (by rw [ite_eq_right h4]; exact cx) R M

/-- **The rotation**: the lanes of the four registers, rotated left by the
low five bits of `ecx`. -/
theorem rotate_wp {s : State} {is : List Instr} {Q : State → Prop}
    {v : Nat → Nat → BitVec 32} {kr : BitVec 32} (hcx : s.gpr .ecx = kr) (hx : ∀ g < 4, s.xmm (xr g) = L (v g))
    (k : ∀ s', Stay s s' → (∀ g < 4, s'.xmm (xr g) = L fun c => (v g c).rotateLeft (kr.toNat % 32)) →
      s'.mem = s.mem → WP isa (.block is) s' Q) :
    WP isa (.block (rotate ++ is)) s Q := by
  rw [show rotate ++ is = rotStep 0 ++ (rotStep 1 ++ (rotStep 2 ++ (rotStep 3 ++ (rotStep 4 ++ is)))) by
    rw [rotate, show (List.range 5).flatMap rotStep = rotStep 0 ++ (rotStep 1 ++ (rotStep 2 ++ (rotStep 3 ++
      (rotStep 4 ++ [])))) from rfl]
    simp only [List.append_assoc, List.append_nil]]
  refine rotStep_wp (by decide) hcx hx fun s₁ t₁ c₁ x₁ m₁ =>
    rotStep_wp (by decide) c₁ x₁ fun s₂ t₂ c₂ x₂ m₂ =>
    rotStep_wp (by decide) c₂ x₂ fun s₃ t₃ c₃ x₃ m₃ =>
    rotStep_wp (by decide) c₃ x₃ fun s₄ t₄ c₄ x₄ m₄ =>
    rotStep_wp (by decide) c₄ x₄ fun s₅ t₅ _ x₅ m₅ =>
    k s₅ ((((t₁.trans t₂).trans t₃).trans t₄).trans t₅) (fun g hg => ?_)
      (m₅.trans (m₄.trans (m₃.trans (m₂.trans m₁))))
  rw [x₅ g hg]
  exact L_congr fun c _ => Proof.Cast5.steps_eq _ _

/-! ## The bytes of the sixteen `I` -/

/-- The four registers of bytes. -/
abbrev ioR (W : BitVec 32) : Region := ⟨slot W 528, 64⟩

/-- The four registers of the bytes of `xmm0` to `xmm3`'s doublewords, to
the working space. -/
theorem planes_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (k : ∀ m' g, (∀ b < 4, m'.readW (slot W (ioOff b)) 128 =
        tr (XBinOp.eval .pshufb (f .xmm0) (cst oT)) (XBinOp.eval .pshufb (f .xmm1) (cst oT))
          (XBinOp.eval .pshufb (f .xmm2) (cst oT)) (XBinOp.eval .pshufb (f .xmm3) (cst oT)) b) →
      Frame [ioR W] m m' → WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (planes ++ is)) (S s m f) Q := by
  show WP isa (.block (tb .xmm5 oT :: x .pshufb .xmm0 .xmm5 :: x .pshufb .xmm1 .xmm5 :: x .pshufb .xmm2 .xmm5 ::
    x .pshufb .xmm3 .xmm5 :: (transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++
      (stx .esi (ioOff 0) .xmm0 :: stx .esi (ioOff 1) .xmm6 :: stx .esi (ioOff 2) .xmm4 :: stx .esi (ioOff 3) .xmm7 ::
        is)))) _ _
  refine wp_tbE E (by decide) (wp_bin (wp_bin (wp_bin (wp_bin (transpose0_wp fun f2 r0 r1 r2 r3 =>
    wp_stW E (by decide) (wp_stW E (by decide) (wp_stW E (by decide) (wp_stW E (by decide) ?_))))))))
  simp only [upd, reduceCtorEq, ↓reduceIte] at r0 r1 r2 r3
  rw [r0, r1, r2, r3]
  have hc : ∀ o, 528 ≤ o → o + 16 ≤ 592 → (ioR W).Contains (slot W o) (128 / 8) := fun o h h' =>
    Offset.contains _ h (by omega) (by decide)
  refine k _ _ (fun b hb => ?_) (((((Frame.refl _ _).writeW List.mem_cons_self _ (hc _ (by decide)
    (by decide))).writeW List.mem_cons_self _ (hc _ (by decide) (by decide))).writeW List.mem_cons_self _
    (hc _ (by decide) (by decide))).writeW List.mem_cons_self _ (hc _ (by decide) (by decide)))
  rcases cases4 hb with rfl | rfl | rfl | rfl
  · rw [rd_wr _ W _ (by decide) (by decide) (by decide), rd_wr _ W _ (by decide) (by decide) (by decide),
      rd_wr _ W _ (by decide) (by decide) (by decide), readW_self128]
  · rw [rd_wr _ W _ (by decide) (by decide) (by decide), rd_wr _ W _ (by decide) (by decide) (by decide),
      readW_self128]
  · rw [rd_wr _ W _ (by decide) (by decide) (by decide), readW_self128]
  · rw [readW_self128]

/-! ## An S-box of the sixteen blocks -/

/-- S-box `j`'s entries. -/
abbrev enR (W : BitVec 32) (j : Nat) : Region := ⟨slot W (592 + 64 * j), 64⟩

/-- The entries of S-box `j` for a group of four blocks, from the planes'
bytes: doubleword `c` is the S-box's entry at byte `4 gI + c` of the
register `IO` of the bytes that index it. -/
theorem en_dword {m1 : Mem} {W : BitVec 32} {t : Nat → BitVec 8} {IO : BitVec 128} {j gI c : Nat} (hj : j < 4)
    (hgI : gI < 4) (hc : c < 4) (hIO : ∀ i < 16, byte IO i = t i)
    (hV : ∀ r < 16, vAt m1 W r = ByteLookup.idx (cst (oC r))
      (XBinOp.eval .pand (XShiftOp.eval .psrld IO 4) (cst oM)) (XBinOp.eval .pand IO (cst oM))) :
    dword (XBinOp.eval .pshufb (tr (ByteLookup.acc (rowC j 0) (vAt m1 W) 15)
      (ByteLookup.acc (rowC j 1) (vAt m1 W) 15) (ByteLookup.acc (rowC j 2) (vAt m1 W) 15)
      (ByteLookup.acc (rowC j 3) (vAt m1 W) 15) gI) (cst oT)) c = sboxOf j (t (4 * gI + c)) := by
  refine word_ext fun p hp => ?_
  rw [byte_of_dword _ _ hp]
  refine (byte_entries (a := fun p => ByteLookup.acc (rowC j p) (vAt m1 W) 15) cst_T hgI hc hp).trans ?_
  exact acc_entry hj hp (by omega) hV ((byte_hi (by omega) (cst_M _ (by omega))).trans (by rw [hIO _ (by omega)]))
    ((byte_lo (cst_M _ (by omega))).trans (by rw [hIO _ (by omega)]))

theorem sbox_eq (j : Nat) (is : List Instr) : Impl.Cast5.X86.Ssse3.Wide.sbox j ++ is =
    ld .xmm0 .esi (ioOff (3 - j)) :: tb .xmm2 oM :: x .movdqa .xmm1 .xmm0 :: .xop (.shift .psrld .xmm1 4) ::
      x .pand .xmm1 .xmm2 :: x .pand .xmm0 .xmm2 :: ((List.range' 0 16).flatMap index ++ (scan j ++
        (transpose .xmm4 .xmm5 .xmm6 .xmm7 .xmm0 .xmm1 .xmm2 .xmm3 ++ (tb .xmm5 oT :: x .pshufb .xmm4 .xmm5 ::
          x .pshufb .xmm2 .xmm5 :: x .pshufb .xmm0 .xmm5 :: x .pshufb .xmm3 .xmm5 :: stx .esi (enOff j 0) .xmm4 ::
          stx .esi (enOff j 1) .xmm2 :: stx .esi (enOff j 2) .xmm0 :: stx .esi (enOff j 3) .xmm3 :: is)))) := by
  rw [Impl.Cast5.X86.Ssse3.Wide.sbox, Impl.Cast5.X86.Ssse3.Wide.nibbles, entries, List.range_eq_range']
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **An S-box's entries of the sixteen blocks**: with the bytes `t` that
index S-box `j` at their place, its entries at them, four a place; only the
index vectors' places and the entries' change. -/
theorem sbox16_wp {K W : BitVec 32} (E : Env16 K W s) {t : Nat → BitVec 8} {f : XReg → BitVec 128}
    {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (hIO : ∀ i < 16, byte (m.readW (slot W (ioOff (3 - j))) 128) i = t i)
    (k : ∀ m' g, Frame [vR W, enR W j] m m' →
      (∀ gI < 4, ∀ c < 4, dword (m'.readW (slot W (enOff j gI)) 128) c = sboxOf j (t (4 * gI + c))) →
      WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (Impl.Cast5.X86.Ssse3.Wide.sbox j ++ is)) (S s m f) Q := by
  rw [sbox_eq]
  refine wp_ldW E (by simp only [ioOff]; omega) (wp_tbE E (by decide) (wp_bin
    (wp_xs rfl (wp_bin (wp_bin (indexes_wp E.env (m₀ := m)
      (H := XBinOp.eval .pand (XShiftOp.eval .psrld (m.readW (slot W (ioOff (3 - j))) 128) 4) (cst oM))
      (L := XBinOp.eval .pand (m.readW (slot W (ioOff (3 - j))) 128) (cst oM)) 16 0 m _ (by decide) rfl rfl
      (fun r' h => absurd h (Nat.not_lt_zero _)) (Frame.refl _ _) fun m1 f1 hV hf1 =>
    scan_wp E.env hj fun f2 hA => transpose4_wp fun f3 r0 r1 r2 r3 => wp_tbE E (by decide) (wp_bin (wp_bin
      (wp_bin (wp_bin (wp_stW E (by simp only [enOff]; omega) (wp_stW E (by simp only [enOff]; omega)
      (wp_stW E (by simp only [enOff]; omega) (wp_stW E (by simp only [enOff]; omega) ?_))))))))))))))
  have a4 : f2 .xmm4 = _ := hA 0 (by decide)
  have a5 : f2 .xmm5 = _ := hA 1 (by decide)
  have a6 : f2 .xmm6 = _ := hA 2 (by decide)
  have a7 : f2 .xmm7 = _ := hA 3 (by decide)
  rw [a4, a5, a6, a7] at r0 r1 r2 r3
  simp only [upd, reduceCtorEq, ↓reduceIte, r0, r1, r2, r3]
  have hc : ∀ o, 592 + 64 * j ≤ o → o + 16 ≤ 592 + 64 * j + 64 → (enR W j).Contains (slot W o) (128 / 8) :=
    fun o h h' => Offset.contains _ h (by omega) (by omega)
  have me : enR W j ∈ [vR W, enR W j] := List.mem_cons_of_mem _ List.mem_cons_self
  refine k _ _ (((((hf1.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self).writeW
    me _ (hc (enOff j 0) (by simp only [enOff]; omega) (by simp only [enOff]; omega))).writeW me _
    (hc (enOff j 1) (by simp only [enOff]; omega) (by simp only [enOff]; omega))).writeW me _
    (hc (enOff j 2) (by simp only [enOff]; omega) (by simp only [enOff]; omega))).writeW me _
    (hc (enOff j 3) (by simp only [enOff]; omega) (by simp only [enOff]; omega))) fun gI hgI c hc' => ?_
  rcases cases4 hgI with rfl | rfl | rfl | rfl
  · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      readW_self128]
    exact en_dword hj (by decide) hc' hIO fun r hr => hV r (by omega)
  · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      readW_self128]
    exact en_dword hj (by decide) hc' hIO fun r hr => hV r (by omega)
  · rw [rd_wr _ W _ (by simp only [enOff]; omega) (by simp only [enOff]; omega) (by simp only [enOff]; omega),
      readW_self128]
    exact en_dword hj (by decide) hc' hIO fun r hr => hV r (by omega)
  · rw [readW_self128]
    exact en_dword hj (by decide) hc' hIO fun r hr => hV r (by omega)

/-! ## `f` from the four S-boxes' entries -/

/-- An operation of `f`: exclusive or, sum or difference. -/
def fo (o : Nat) (a b : BitVec 32) : BitVec 32 :=
  match o with
  | 0 => a ^^^ b
  | 1 => a + b
  | _ => a - b

theorem sub_lane (a b : BitVec 32) : a + (b ^^^ 0xFFFFFFFF#32) + 1#32 = a - b := by
  rw [show (0xFFFFFFFF#32) = BitVec.allOnes 32 from rfl, BitVec.xor_allOnes, BitVec.add_assoc,
    ← BitVec.neg_eq_not_add, BitVec.sub_eq_add_neg]

/-- A store of a register whose value is known. -/
theorem wp_stV {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {r : XReg} {o : Nat} {v : BitVec 128} (ho' : o + 16 ≤ 848) (hv : f r = v)
    (k : WP isa (.block is) (S s (m.writeW (slot W o) v) f) Q) :
    WP isa (.block (stx .esi o r :: is)) (S s m f) Q := by
  subst hv; exact wp_stW E ho' k

/-- An operation of `f` on the lanes of `a` and `xmm4`. -/
theorem fOp_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {o : Nat} {a : XReg}
    (ha4 : a ≠ .xmm4) (ha7 : a ≠ .xmm7) (h6 : f .xmm6 = cst oOnes) (h7 : f .xmm7 = cst oOne)
    (k : ∀ f', (∀ c < 4, dword (f' a) c = fo o (dword (f a) c) (dword (f .xmm4) c)) →
      (∀ q, q ≠ a → q ≠ .xmm4 → f' q = f q) → WP isa (.block is) (S s m f') Q) :
    WP isa (.block (fOp o a ++ is)) (S s m f) Q := by
  match o with
  | 0 => exact wp_bin (k _ (fun c _ => by rw [upd_self, dword_pxor]; rfl) fun q hq _ => upd_ne _ _ hq)
  | 1 => exact wp_bin (k _ (fun c hc => by rw [upd_self, dword_paddd _ _ hc]; rfl) fun q hq _ => upd_ne _ _ hq)
  | n + 2 =>
    refine wp_bin (wp_bin (wp_bin (k _ (fun c hc => ?_) fun q hq h4 => ?_)))
    · rw [upd_self, upd_self, upd_ne _ _ ha4, upd_ne _ _ ha7.symm, upd_self,
        upd_ne _ _ (show (.xmm7 : XReg) ≠ .xmm4 by decide), dword_paddd _ _ hc, dword_paddd _ _ hc, dword_pxor, h6,
        h7, cst_Ones c hc, cst_One c hc]
      exact sub_lane _ _
    · rw [upd_ne _ _ hq, upd_ne _ _ hq, upd_ne _ _ h4]

/-- `f` of the blocks `4g` to `4g + 3`, and their halves' exchange. -/
theorem combG_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {o1 o2 o3 g : Nat} (hg : g < 4) (h6 : f .xmm6 = cst oOnes) (h7 : f .xmm7 = cst oOne)
    (k : ∀ f' v, (∀ c < 4, dword v c = dword (m.readW (slot W (lOff g)) 128) c ^^^
        fo o3 (fo o2 (fo o1 (dword (m.readW (slot W (enOff 0 g)) 128) c)
          (dword (m.readW (slot W (enOff 1 g)) 128) c)) (dword (m.readW (slot W (enOff 2 g)) 128) c))
          (dword (m.readW (slot W (enOff 3 g)) 128) c)) →
      f' .xmm6 = cst oOnes → f' .xmm7 = cst oOne →
      WP isa (.block is) (S s ((m.writeW (slot W (lOff g)) (m.readW (slot W (rOff g)) 128)).writeW
        (slot W (rOff g)) v) f') Q) :
    WP isa (.block (combG o1 o2 o3 g ++ is)) (S s m f) Q := by
  obtain ⟨n4, n5, n6, n7⟩ := xr_lt4_ne hg
  have c64 : (.xmm6 : XReg) ≠ .xmm4 := by decide
  have c74 : (.xmm7 : XReg) ≠ .xmm4 := by decide
  have c65 : (.xmm6 : XReg) ≠ .xmm5 := by decide
  have c75 : (.xmm7 : XReg) ≠ .xmm5 := by decide
  rw [combG]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldW E (by simp only [enOff]; omega) (wp_ldW E (by simp only [enOff]; omega)
    (fOp_wp n4 n7 (by rw [upd_ne _ _ c64, upd_ne _ _ n6.symm]; exact h6)
      (by rw [upd_ne _ _ c74, upd_ne _ _ n7.symm]; exact h7) fun f1 d1 p1 =>
    wp_ldW E (by simp only [enOff]; omega)
    (fOp_wp n4 n7 (by rw [upd_ne _ _ c64, p1 _ n6.symm c64, upd_ne _ _ c64, upd_ne _ _ n6.symm]; exact h6)
      (by rw [upd_ne _ _ c74, p1 _ n7.symm c74, upd_ne _ _ c74, upd_ne _ _ n7.symm]; exact h7) fun f2 d2 p2 =>
    wp_ldW E (by simp only [enOff]; omega)
    (fOp_wp n4 n7
      (by rw [upd_ne _ _ c64, p2 _ n6.symm c64, upd_ne _ _ c64, p1 _ n6.symm c64, upd_ne _ _ c64,
        upd_ne _ _ n6.symm]; exact h6)
      (by rw [upd_ne _ _ c74, p2 _ n7.symm c74, upd_ne _ _ c74, p1 _ n7.symm c74, upd_ne _ _ c74,
        upd_ne _ _ n7.symm]; exact h7) fun f3 d3 p3 =>
    wp_ldW E (by simp only [lOff]; omega) (wp_bin (wp_ldW E (by simp only [rOff]; omega)
    (wp_stV E (by simp only [lOff]; omega) (v := m.readW (slot W (rOff g)) 128) (upd_self _ _ _)
    (wp_stV E (by simp only [rOff]; omega)
      (v := XBinOp.eval .pxor (f3 (xr g)) (m.readW (slot W (lOff g)) 128))
      (by rw [upd_ne _ _ n5, upd_self, upd_ne _ _ n4, upd_self]) (k _ _ (fun c hc => ?_) ?_ ?_)))))))))
  · have e1 := d1 c hc
    have e2 := d2 c hc
    have e3 := d3 c hc
    simp only [upd_self, upd_ne _ _ n4] at e1 e2 e3
    rw [dword_pxor, e3, e2, e1]
    exact BitVec.xor_comm _ _
  · rw [upd_ne _ _ c65, upd_ne _ _ n6.symm, upd_ne _ _ c64, p3 _ n6.symm c64, upd_ne _ _ c64, p2 _ n6.symm c64,
      upd_ne _ _ c64, p1 _ n6.symm c64, upd_ne _ _ c64, upd_ne _ _ n6.symm]; exact h6
  · rw [upd_ne _ _ c75, upd_ne _ _ n7.symm, upd_ne _ _ c74, p3 _ n7.symm c74, upd_ne _ _ c74, p2 _ n7.symm c74,
      upd_ne _ _ c74, p1 _ n7.symm c74, upd_ne _ _ c74, upd_ne _ _ n7.symm]; exact h7

/-- The halves' places. -/
abbrev lrR (W : BitVec 32) : Region := ⟨slot W 128, 128⟩

/-- `f` of the blocks of the group `g`, in `m`, by the operations `o1`, `o2`, `o3`. -/
abbrev fv (o1 o2 o3 : Nat) (m : Mem) (W : BitVec 32) (g c : Nat) : BitVec 32 :=
  fo o3 (fo o2 (fo o1 (dword (m.readW (slot W (enOff 0 g)) 128) c) (dword (m.readW (slot W (enOff 1 g)) 128) c))
    (dword (m.readW (slot W (enOff 2 g)) 128) c)) (dword (m.readW (slot W (enOff 3 g)) 128) c)

/-- `f` and the exchange for the groups `g` to `g + n - 1`. -/
theorem combs_wp {K W : BitVec 32} (E : Env16 K W s) {is : List Instr} {Q : State → Prop} {m₀ : Mem}
    {o1 o2 o3 : Nat} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 →
      f .xmm6 = cst oOnes → f .xmm7 = cst oOne →
      (∀ g' < g, m.readW (slot W (lOff g')) 128 = m₀.readW (slot W (rOff g')) 128 ∧
        ∀ c < 4, dword (m.readW (slot W (rOff g')) 128) c =
          dword (m₀.readW (slot W (lOff g')) 128) c ^^^ fv o1 o2 o3 m₀ W g' c) →
      (∀ g', g ≤ g' → g' < 4 → m.readW (slot W (lOff g')) 128 = m₀.readW (slot W (lOff g')) 128 ∧
        m.readW (slot W (rOff g')) 128 = m₀.readW (slot W (rOff g')) 128) →
      Same W 592 848 m₀ m → Frame [lrR W] m₀ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (lOff g')) 128 = m₀.readW (slot W (rOff g')) 128 ∧
          ∀ c < 4, dword (m'.readW (slot W (rOff g')) 128) c =
            dword (m₀.readW (slot W (lOff g')) 128) c ^^^ fv o1 o2 o3 m₀ W g' c) →
        Frame [lrR W] m₀ m' → WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap (combG o1 o2 o3) ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ hd _ _ hf k => k m f hd hf
  | succ n ih =>
    intro g m f hn h6 h7 hd hu hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine combG_wp E (by omega) h6 h7 fun f' v hv a6 a7 => ?_
    have hc : ∀ o, 128 ≤ o → o + 16 ≤ 256 → (lrR W).Contains (slot W o) (128 / 8) := fun o h h' =>
      Offset.contains _ h (by omega) (by decide)
    refine ih (g + 1) _ f' (by omega) a6 a7 (fun g' hg' => ?_) (fun g' h1 h2 => ?_)
      ((hs.write _ (.inl (by simp only [lOff]; omega)) (by decide) (by simp only [lOff]; omega)).write _
        (.inl (by simp only [rOff]; omega)) (by decide) (by simp only [rOff]; omega))
      ((hf.writeW List.mem_cons_self _ (hc (lOff g) (by simp only [lOff]; omega)
        (by simp only [lOff]; omega))).writeW List.mem_cons_self _ (hc (rOff g) (by simp only [rOff]; omega)
        (by simp only [rOff]; omega)))
      fun m' f'' hd' hf' => k m' f'' (fun g' hg' => hd' g' (by omega)) hf'
    · by_cases e : g' = g
      · subst e
        refine ⟨?_, fun c hc' => ?_⟩
        · rw [rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [lOff]; omega)
            (by simp only [rOff]; omega), readW_self128]
          exact (hu g' (Nat.le_refl _) (by omega)).2
        · rw [readW_self128, hv c hc', (hu g' (Nat.le_refl _) (by omega)).1, fv,
            hs (enOff 0 g') (by simp only [enOff]; omega) (by simp only [enOff]; omega),
            hs (enOff 1 g') (by simp only [enOff]; omega) (by simp only [enOff]; omega),
            hs (enOff 2 g') (by simp only [enOff]; omega) (by simp only [enOff]; omega),
            hs (enOff 3 g') (by simp only [enOff]; omega) (by simp only [enOff]; omega)]
      · obtain ⟨a, b⟩ := hd g' (by omega)
        refine ⟨?_, fun c hc' => ?_⟩
        · rw [rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [lOff]; omega)
            (by simp only [rOff]; omega), rd_wr _ W _ (by simp only [lOff]; omega) (by simp only [lOff]; omega)
            (by simp only [lOff]; omega)]
          exact a
        · rw [rd_wr _ W _ (by simp only [rOff]; omega) (by simp only [rOff]; omega)
            (by simp only [rOff]; omega), rd_wr _ W _ (by simp only [lOff, rOff]; omega)
            (by simp only [rOff]; omega) (by simp only [lOff]; omega)]
          exact b c hc'
    · obtain ⟨a, b⟩ := hu g' (by omega) h2
      refine ⟨?_, ?_⟩
      · rw [rd_wr _ W _ (by simp only [lOff, rOff]; omega) (by simp only [lOff]; omega)
          (by simp only [rOff]; omega), rd_wr _ W _ (by simp only [lOff]; omega) (by simp only [lOff]; omega)
          (by simp only [lOff]; omega)]
        exact a
      · rw [rd_wr _ W _ (by simp only [rOff]; omega) (by simp only [rOff]; omega)
          (by simp only [rOff]; omega), rd_wr _ W _ (by simp only [lOff, rOff]; omega)
          (by simp only [rOff]; omega) (by simp only [lOff]; omega)]
        exact b

/-! ## `I` before its rotation -/

theorem rsub_lane (km d : BitVec 32) : (d ^^^ 0xFFFFFFFF#32) + (km + 1#32) = km - d := by
  rw [← sub_lane, BitVec.add_comm (d ^^^ _), BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 1#32]

/-- `Km`, in every lane, combined with `D` by `op`. -/
theorem mix12_wp {K W : BitVec 32} (E : Env16 K W s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {op : XBinOp}
    (k : ∀ g, (∀ gI < 4, g (xr gI) =
        XBinOp.eval op (m.readW (slot W (rOff gI)) 128) (shufDwords ((0 : BitVec 96) ++ s.gpr .eax) 0)) →
      WP isa (.block is) (S s m g) Q) :
    WP isa (.block (bcKm ++ ((List.range 4).flatMap (mixG op) ++ is))) (S s m f) Q := by
  rw [range4]
  show WP isa (.block (.xop (.movd .xmm7 .eax) :: .xop (.pshufd .xmm7 .xmm7 0) :: ld .xmm0 .esi (rOff 0) ::
    x op .xmm0 .xmm7 :: ld .xmm1 .esi (rOff 1) :: x op .xmm1 .xmm7 :: ld .xmm2 .esi (rOff 2) :: x op .xmm2 .xmm7 ::
    ld .xmm3 .esi (rOff 3) :: x op .xmm3 .xmm7 :: is)) _ _
  refine wp_xs rfl (wp_xs rfl (wp_ldW E (by decide) (wp_bin (wp_ldW E (by decide) (wp_bin (wp_ldW E (by decide)
    (wp_bin (wp_ldW E (by decide) (wp_bin (k _ fun gI hgI => ?_))))))))))
  rcases cases4 hgI with rfl | rfl | rfl | rfl
  · rw [show xr 0 = XReg.xmm0 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]
  · rw [show xr 1 = XReg.xmm1 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]
  · rw [show xr 2 = XReg.xmm2 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]
  · rw [show xr 3 = XReg.xmm3 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]

/-- `Km - D`, as `~D + (Km + 1)`. -/
theorem mix3_wp {K W : BitVec 32} {u : State} (E : Env16 K W u) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', Stay u u' → u'.gpr .ecx = u.gpr .ecx → u'.mem = u.mem →
      (∀ gI < 4, u'.xmm (xr gI) = XBinOp.eval .paddd
        (XBinOp.eval .pxor (u.mem.readW (slot W (rOff gI)) 128) (cst oOnes))
        (shufDwords ((0 : BitVec 96) ++ (u.gpr .eax + BitVec.ofNat 32 1)) 0)) → WP isa (.block is) u' Q) :
    WP isa (.block (Impl.Cast5.X86.Ssse3.Wide.mix 3 ++ is)) u Q := by
  show WP isa (.block (.alu .add .eax (imm 1) :: .xop (.movd .xmm7 .eax) :: .xop (.pshufd .xmm7 .xmm7 0) ::
    tb .xmm6 oOnes :: ld .xmm0 .esi (rOff 0) :: x .pxor .xmm0 .xmm6 :: x .paddd .xmm0 .xmm7 ::
    ld .xmm1 .esi (rOff 1) :: x .pxor .xmm1 .xmm6 :: x .paddd .xmm1 .xmm7 :: ld .xmm2 .esi (rOff 2) ::
    x .pxor .xmm2 .xmm6 :: x .paddd .xmm2 .xmm7 :: ld .xmm3 .esi (rOff 3) :: x .pxor .xmm3 .xmm6 ::
    x .paddd .xmm3 .xmm7 :: is)) u Q
  refine wp_addix fun u₁ a₁ x₁ => ?_
  have E₁ := E.stay (Stay.upd a₁ (.inl rfl))
  show WP isa _ (S u₁ u₁.mem u₁.xmm) _
  refine wp_xs rfl (wp_xs rfl (wp_tbE E₁ (by decide) (wp_ldW E₁ (by decide) (wp_bin (wp_bin (wp_ldW E₁ (by decide)
    (wp_bin (wp_bin (wp_ldW E₁ (by decide) (wp_bin (wp_bin (wp_ldW E₁ (by decide) (wp_bin (wp_bin
    (k _ ((Stay.upd a₁ (.inl rfl)).trans (Stay.S _ _ _)) (a₁.other _ (by decide)) a₁.mem fun gI hgI => ?_)))))))))))))))
  rcases cases4 hgI with rfl | rfl | rfl | rfl
  · rw [show xr 0 = XReg.xmm0 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]; rw [a₁.mem, a₁.gpr]
  · rw [show xr 1 = XReg.xmm1 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]; rw [a₁.mem, a₁.gpr]
  · rw [show xr 2 = XReg.xmm2 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]; rw [a₁.mem, a₁.gpr]
  · rw [show xr 3 = XReg.xmm3 from rfl]; simp only [upd, reduceCtorEq, ↓reduceIte]; rw [a₁.mem, a₁.gpr]

/-- **`I` before its rotation**, by the round's type: lane `c` of register
`g` is `mix t Km D` for `D` of block `4g + c`. -/
theorem mix_wp {K W : BitVec 32} {u : State} (E : Env16 K W u) {is : List Instr} {Q : State → Prop} {t : Nat}
    (ht : t = 1 ∨ t = 2 ∨ t = 3) {km : BitVec 32} (hax : u.gpr .eax = km)
    (k : ∀ u', Stay u u' → u'.gpr .ecx = u.gpr .ecx → u'.mem = u.mem →
      (∀ g < 4, u'.xmm (xr g) =
        L fun c => Proof.Cast5.mix t km (dword (u.mem.readW (slot W (rOff g)) 128) c)) →
      WP isa (.block is) u' Q) :
    WP isa (.block (Impl.Cast5.X86.Ssse3.Wide.mix t ++ is)) u Q := by
  rcases ht with rfl | rfl | rfl
  · show WP isa (.block (bcKm ++ ((List.range 4).flatMap (mixG .paddd) ++ is))) (S u u.mem u.xmm) Q
    refine mix12_wp E fun g hx => k _ (Stay.S _ _ _) rfl rfl fun gI hgI => ?_
    show g (xr gI) = _
    rw [hx gI hgI, hax, bcast_L]
    exact L_ext fun c hc => by rw [dword_paddd _ _ hc, dword_L _ hc]; exact BitVec.add_comm _ _
  · show WP isa (.block (bcKm ++ ((List.range 4).flatMap (mixG .pxor) ++ is))) (S u u.mem u.xmm) Q
    refine mix12_wp E fun g hx => k _ (Stay.S _ _ _) rfl rfl fun gI hgI => ?_
    show g (xr gI) = _
    rw [hx gI hgI, hax, bcast_L]
    exact L_ext fun c hc => by rw [dword_pxor, dword_L _ hc]; exact BitVec.xor_comm _ _
  · refine mix3_wp E fun u' st cx mm hx => k u' st cx mm fun gI hgI => ?_
    rw [hx gI hgI, hax, bcast_L]
    exact L_ext fun c hc => by
      rw [dword_paddd _ _ hc, dword_pxor, dword_L _ hc, cst_Ones c hc]; exact rsub_lane _ _

/-! ## The round's number, its type and its subkeys -/

open VG.Proof.Cast5.X86 (WP.keep Keep)

/-- The round's type, as the code computes it from the round's number less
one: `i - 3 (11 i / 32)` for `i` the number. -/
def tyOf (R : BitVec 32) : BitVec 32 :=
  R + 1#32 - ((R + 1#32 + (R + 1#32 + (R + 1#32)) + (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32)) +
    (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32))))) >>> 5 +
    (R + 1#32 + (R + 1#32 + (R + 1#32)) + (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32)) +
    (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32))))) >>> 5 +
    (R + 1#32 + (R + 1#32 + (R + 1#32)) + (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32)) +
    (R + 1#32 + (R + 1#32) + (R + 1#32 + (R + 1#32))))) >>> 5)

/-- It is the number modulo 3, for the sixteen rounds. -/
theorem tyOf_eq : ∀ r < 16, tyOf (BitVec.ofNat 32 r) = BitVec.ofNat 32 ((r + 1) % 3) ∧
    (tyOf (BitVec.ofNat 32 r) - 1#32 == 0) = decide ((r + 1) % 3 = 1) ∧
    (tyOf (BitVec.ofNat 32 r) - 2#32 == 0) = decide ((r + 1) % 3 = 2) := by decide

theorem roundType_run {K W : BitVec 32} {u : State} {R km kr : BitVec 32} (hsi : u.gpr .esi = W)
    (hbp : u.gpr .ebp = K) (a1 : InRegions (u.rd ++ u.wr) (addr W rnOff) 4)
    (v1 : u.mem.readW (addr W rnOff) 32 = R)
    (a2 : InRegions (u.rd ++ u.wr) (addr (R + R + (R + R) + K) 64) 4)
    (v2 : u.mem.readW (addr (R + R + (R + R) + K) 64) 32 = kr)
    (a3 : InRegions (u.rd ++ u.wr) (addr (R + R + (R + R) + K) 0) 4)
    (v3 : u.mem.readW (addr (R + R + (R + R) + K) 0) 32 = km) :
    WP isa (.block roundType) u fun v => v.gpr .ebx = tyOf R ∧ v.gpr .eax = km ∧ v.gpr .ecx = kr ∧
      v.zf = some (tyOf R - 1#32 == 0) ∧ v.mem = u.mem ∧ v.xmm = u.xmm := by
  unfold roundType
  crun [hsi, hbp, a1, v1, a2, v2, a3, v3, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, RegUpd.xmm_arithFlags]
  exact ⟨rfl, rfl⟩

/-- **The round's type, `Km` and `Kr`**, for the round whose number less one
is `r`. -/
theorem roundType_wp {K W : BitVec 32} {u : State} (E : Env16 K W u) {r : Nat} (hr : r < 16) {km kr : BitVec 32}
    (hrn : u.mem.readW (slot W rnOff) 32 = BitVec.ofNat 32 r) (hkm : u.mem.readW (slot K (4 * r)) 32 = km)
    (hkr : u.mem.readW (slot K (4 * r + 64)) 32 = kr) :
    WP isa (.block roundType) u fun v =>
      (v.gpr .ebx = tyOf (BitVec.ofNat 32 r) ∧ v.gpr .eax = km ∧ v.gpr .ecx = kr ∧
        v.zf = some (tyOf (BitVec.ofNat 32 r) - 1#32 == 0) ∧ v.mem = u.mem ∧ v.xmm = u.xmm) ∧
      Keep [.eax, .ecx, .ebx] u v ∧ v.syms = u.syms := by
  have fW := E.fW
  have fK := E.fK
  have eA : addr W rnOff = slot W rnOff := addr_eq (by simp only [rnOff]; omega)
  have eK : BitVec.ofNat 32 r + BitVec.ofNat 32 r + (BitVec.ofNat 32 r + BitVec.ofNat 32 r) + K =
      K + BitVec.ofNat 32 (4 * r) := by
    rw [BitVec.add_comm _ K, ← BitVec.ofNat_add, ← BitVec.ofNat_add, show r + r + (r + r) = 4 * r by omega]
  have eK0 : addr (K + BitVec.ofNat 32 (4 * r)) 0 = slot K (4 * r) := by
    show (K + BitVec.ofNat 32 (4 * r) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [Offset.add_add]; exact addr_eq (by omega)
  have eK64 : addr (K + BitVec.ofNat 32 (4 * r)) 64 = slot K (4 * r + 64) := by
    show (K + BitVec.ofNat 32 (4 * r) + BitVec.ofNat 32 64).setWidth 64 = _
    rw [Offset.add_add]; exact addr_eq (by omega)
  exact WP.mono_syms (WP.keep [.eax, .ecx, .ebx] (roundType_run E.esi E.ebp (by rw [eA]; exact E.rdW (by decide))
    (by rw [eA]; exact hrn) (by rw [eK, eK64]; exact E.rdK _ _ (by omega)) (by rw [eK, eK64]; exact hkr)
    (by rw [eK, eK0]; exact E.rdK _ _ (by omega)) (by rw [eK, eK0]; exact hkm)) (by decide))
    fun v ⟨h, hk⟩ hs => ⟨h, hk, hs⟩

/-- The next round's number, and the count down. -/
theorem next_run {W : BitVec 32} {u : State} {rn st cn : BitVec 32} (hsi : u.gpr .esi = W)
    (a1 : InRegions (u.rd ++ u.wr) (addr W rnOff) 4) (v1 : u.mem.readW (addr W rnOff) 32 = rn)
    (a2 : InRegions (u.rd ++ u.wr) (addr W stOff) 4) (v2 : u.mem.readW (addr W stOff) 32 = st)
    (a3 : InRegions (u.rd ++ u.wr) (addr W cnOff) 4)
    (v3 : (u.mem.writeW (addr W rnOff) (rn + st)).readW (addr W cnOff) 32 = cn)
    (w1 : InRegions u.wr (addr W rnOff) 4) (w3 : InRegions u.wr (addr W cnOff) 4) :
    WP isa (.block next) u fun v => v.zf = some (cn - 1#32 == 0) ∧
      v.mem = (u.mem.writeW (addr W rnOff) (rn + st)).writeW (addr W cnOff) (cn - 1#32) ∧ v.xmm = u.xmm := by
  unfold next
  crun [hsi, a1, v1, a2, v2, a3, v3, w1, w3, RegUpd.xmm_setReg, RegUpd.xmm_setFlags, RegUpd.xmm_arithFlags]

/-- A doubleword of the working space read through a store of a doubleword
elsewhere in it. -/
theorem rd4_wr4 (m : Mem) (W : BitVec 32) {a b : Nat} (v : BitVec 32) (h : a + 4 ≤ b ∨ b + 4 ≤ a)
    (ha : a ≤ 4096) (hb : b ≤ 4096) : (m.writeW (slot W b) v).readW (slot W a) 32 = m.readW (slot W a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- A sixteen-byte place read through a store of a doubleword elsewhere. -/
theorem rd16_wr4 (m : Mem) (W : BitVec 32) {a b : Nat} (v : BitVec 32) (h : a + 16 ≤ b ∨ b + 4 ≤ a)
    (ha : a ≤ 4096) (hb : b ≤ 4096) : (m.writeW (slot W b) v).readW (slot W a) 128 = m.readW (slot W a) 128 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- **The next round's number and the count of rounds left**, in the working
space. -/
theorem next_wp {K W : BitVec 32} {u : State} (E : Env16 K W u) {rn st cn : BitVec 32}
    (h1 : u.mem.readW (slot W rnOff) 32 = rn) (h2 : u.mem.readW (slot W stOff) 32 = st)
    (h3 : u.mem.readW (slot W cnOff) 32 = cn) :
    WP isa (.block next) u fun v =>
      (v.zf = some (cn - 1#32 == 0) ∧
        v.mem = (u.mem.writeW (slot W rnOff) (rn + st)).writeW (slot W cnOff) (cn - 1#32) ∧ v.xmm = u.xmm) ∧
      Keep [.eax, .ecx] u v ∧ v.syms = u.syms := by
  have fW := E.fW
  have e1 : addr W rnOff = slot W rnOff := addr_eq (by simp only [rnOff]; omega)
  have e2 : addr W stOff = slot W stOff := addr_eq (by simp only [stOff]; omega)
  have e3 : addr W cnOff = slot W cnOff := addr_eq (by simp only [cnOff]; omega)
  have h := WP.mono_syms (WP.keep [.eax, .ecx] (next_run (rn := rn) (st := st) (cn := cn) E.esi
    (by rw [e1]; exact E.rdW (by decide)) (by rw [e1]; exact h1) (by rw [e2]; exact E.rdW (by decide))
    (by rw [e2]; exact h2) (by rw [e3]; exact E.rdW (by decide))
    (by rw [e1, e3, rd4_wr4 _ W _ (by decide) (by decide) (by decide)]; exact h3)
    (by rw [e1]; exact E.wrW _ _ (by decide)) (by rw [e3]; exact E.wrW _ _ (by decide))) (by decide))
    fun v ⟨hv, hk⟩ hs => (⟨hv, hk, hs⟩ : (v.zf = some (cn - 1#32 == 0) ∧
      v.mem = (u.mem.writeW (addr W rnOff) (rn + st)).writeW (addr W cnOff) (cn - 1#32) ∧ v.xmm = u.xmm) ∧
      Keep [.eax, .ecx] u v ∧ v.syms = u.syms)
  rw [e1, e3] at h
  exact h

/-! ## The code by the round's type -/

theorem ty_cmp2 : ∀ t < 3, (BitVec.ofNat 32 t - 2#32 == 0) = decide (t = 2) := by decide

/-- Code chosen by the round's type, which is in `ebx`, after its
comparison with 1: the code of the type `tt` (1, 2 or 3) that is `t` modulo
3. -/
theorem byType_wp {f : Nat → List Instr} {v : State} {Q : State → Prop} {t : Nat} (ht : t < 3)
    (hz : v.zf = some (decide (t = 1))) (hb : v.gpr .ebx = BitVec.ofNat 32 t)
    (k : ∀ v' tt, (tt = 1 ∨ tt = 2 ∨ tt = 3) → tt % 3 = t → Fupd v v' → v'.xmm = v.xmm →
      WP isa (.block (f tt)) v' Q) :
    WP isa (byType f) v Q := by
  refine WP.ite (decide (t = 1)) hz
    (fun h => k v 1 (.inl rfl) (by have : t = 1 := by simpa using h
                                   omega) ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)
    fun h => WP.seq (wp_cmpix fun v' fu z x => WP.block_nil ?_)
  have h1 : ¬ t = 1 := by simpa using h
  rw [hb, ty_cmp2 t ht] at z
  refine WP.ite (decide (t = 2)) z
    (fun h2 => k v' 2 (.inr (.inl rfl)) (by have : t = 2 := by simpa using h2
                                            omega) fu x)
    fun h2 => k v' 3 (.inr (.inr rfl)) ?_ fu x
  have h2' : ¬ t = 2 := by simpa using h2
  omega

/-- The operations of `f`, by the round's type. -/
def ops (t : Nat) : Nat × Nat × Nat :=
  match t with
  | 1 => (0, 2, 1)
  | 2 => (2, 1, 0)
  | _ => (1, 0, 2)

theorem comb_eq {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (is : List Instr) :
    Impl.Cast5.X86.Ssse3.Wide.comb t ++ is = tb .xmm6 oOnes :: tb .xmm7 oOne ::
      ((List.range' 0 4).flatMap (combG (ops t).1 (ops t).2.1 (ops t).2.2) ++ is) := by
  rcases ht with rfl | rfl | rfl <;>
    simp only [Impl.Cast5.X86.Ssse3.Wide.comb, ops, List.range_eq_range', List.cons_append, List.nil_append]

theorem fo_comb {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (a b c d : BitVec 32) :
    fo (ops t).2.2 (fo (ops t).2.1 (fo (ops t).1 a b) c) d = Proof.Cast5.comb (t % 3) a b c d := by
  rcases ht with rfl | rfl | rfl <;> rfl

theorem mix_mod {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (km d : BitVec 32) :
    Proof.Cast5.mix t km d = Proof.Cast5.mix (t % 3) km d := by
  rcases ht with rfl | rfl | rfl <;> rfl

/-! ## The rounds in order -/

open VG.Spec.Cast5 (Schedule)
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ f_eq roundI)

/-- The number, less one, of the round after `i` rounds of `n`. -/
def rnd (up : Bool) (n i : Nat) : Nat := if up then i else n - 1 - i

/-- The halves after `i` rounds. -/
def fold (up : Bool) (k : Schedule) (n i : Nat) (lr : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  if up then encFold k i lr else decFold k n i lr

theorem fold_succ (up : Bool) (k : Schedule) {n i : Nat} (hi : i < n) (lr : BitVec 32 × BitVec 32) :
    fold up k n (i + 1) lr = Spec.Cast5.round k (rnd up n i + 1) (fold up k n i lr) := by
  cases up
  · simp only [fold, rnd, Bool.false_eq_true, ite_false]
    rw [decFold_succ, show n - 1 - i + 1 = n - i by omega]
  · simp only [fold, rnd, ite_true]
    exact encFold_succ k i lr

/-- The step to the next round's number. -/
def stv (up : Bool) : BitVec 32 := if up then 1#32 else 0xFFFFFFFF#32

theorem rnd_step_dec : ∀ n < 17, ∀ i < 17, i + 1 < n →
    BitVec.ofNat 32 (n - 1 - i) + 0xFFFFFFFF#32 = BitVec.ofNat 32 (n - 1 - (i + 1)) := by decide

theorem rnd_step (up : Bool) {n i : Nat} (hn : n ≤ 16) (hi : i + 1 < n) :
    BitVec.ofNat 32 (rnd up n i) + stv up = BitVec.ofNat 32 (rnd up n (i + 1)) := by
  cases up
  · simp only [rnd, stv, Bool.false_eq_true, ite_false]
    exact rnd_step_dec n (by omega) i (by omega) hi
  · simp only [rnd, stv, ite_true]
    rw [← BitVec.ofNat_add]

theorem rnd_lt (up : Bool) {n i : Nat} (hi : i < n) : rnd up n i < n := by
  cases up <;> simp only [rnd, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-! ## A round -/

/-- What does not change while the function runs: the subkeys at `K`, apart
from the working space. -/
structure Fix16 (K W : BitVec 32) (k : Schedule) (s₀ : State) : Prop where
  dKW : Region.Disjoint ⟨K.setWidth 64, 128⟩ (wR16 W)
  key : ∀ i < 32, s₀.mem.readW (slot K (4 * i)) 32 = k.getD i 0

/-- After `i` rounds: the halves of the sixteen blocks, the round's number
and the step in the working space. -/
structure RInv (s₀ : State) (K W : BitVec 32) (k : Schedule) (up : Bool) (n i : Nat) (u : State) : Prop where
  env : Env16 K W u
  esp : u.gpr .esp = s₀.gpr .esp
  edi : u.gpr .edi = s₀.gpr .edi
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  syms : u.syms = s₀.syms
  frame : Frame [wR16 W] s₀.mem u.mem
  hv : ∀ b < 16, hv u.mem W b = fold up k n i (st0 s₀.mem W b)
  rn : i < n → u.mem.readW (slot W rnOff) 32 = BitVec.ofNat 32 (rnd up n i)
  st : u.mem.readW (slot W stOff) 32 = stv up

/-- The look-ups' places: the index vectors, the bytes of `I` and the entries. -/
abbrev wkR (W : BitVec 32) : Region := ⟨slot W 272, 576⟩

theorem keep16 {rs : List Region} {m m' : Mem} {W : BitVec 32} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨slot W o, 16⟩ r) : m'.readW (slot W o) 128 = m.readW (slot W o) 128 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem keep4 {rs : List Region} {m m' : Mem} {W : BitVec 32} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨slot W o, 4⟩ r) : m'.readW (slot W o) 32 = m.readW (slot W o) 32 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- What an S-box's look-ups keep: the places below the index vectors, the
bytes of `I` and the entries of the S-boxes before it, and what is after its
own entries. -/
theorem sbox_keep {m m' : Mem} {W : BitVec 32} {j : Nat} (hj : j < 4) (hf : Frame [vR W, enR W j] m m') {o : Nat}
    (ho : o + 16 ≤ 272 ∨ (528 ≤ o ∧ o + 16 ≤ 592 + 64 * j) ∨ 592 + 64 * j + 64 ≤ o) (ho' : o + 16 ≤ 4096) :
    m'.readW (slot W o) 128 = m.readW (slot W o) 128 :=
  keep16 hf fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Offset.disjoint _ (by omega) (by omega) (by decide)
    · rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The bytes that index S-box `j`, for the lanes `Iv` of the four registers. -/
theorem io_q {m4 m' : Mem} {W : BitVec 32} {X : Nat → BitVec 128} {Iv : Nat → Nat → BitVec 32}
    (hio : ∀ b < 4, m4.readW (slot W (ioOff b)) 128 =
      tr (XBinOp.eval .pshufb (X 0) (cst oT)) (XBinOp.eval .pshufb (X 1) (cst oT))
        (XBinOp.eval .pshufb (X 2) (cst oT)) (XBinOp.eval .pshufb (X 3) (cst oT)) b)
    (hx : ∀ g < 4, X g = L (Iv g)) {j : Nat}
    (hm : m'.readW (slot W (ioOff (3 - j))) 128 = m4.readW (slot W (ioOff (3 - j))) 128) {i : Nat} (hi : i < 16) :
    byte (m'.readW (slot W (ioOff (3 - j))) 128) i = (Iv (i / 4) (i % 4)).extractLsb' (8 * (3 - j)) 8 := by
  rw [hm, hio _ (by omega)]
  have h := byte_planes (X := X) cst_T (g := i / 4) (k := i % 4) (b := 3 - j) (by omega) (Nat.mod_lt _ (by decide))
    (by omega)
  rw [show 4 * (i / 4) + i % 4 = i by omega] at h
  rw [h, hx (i / 4) (by omega), dword_L _ (Nat.mod_lt _ (by decide))]

theorem lookups_eq : lookups = rotate ++ (planes ++ (Impl.Cast5.X86.Ssse3.Wide.sbox 0 ++
    (Impl.Cast5.X86.Ssse3.Wide.sbox 1 ++ (Impl.Cast5.X86.Ssse3.Wide.sbox 2 ++
      (Impl.Cast5.X86.Ssse3.Wide.sbox 3 ++ ([.alu .cmp .ebx (imm 1)] : List Instr)))))) := by
  simp only [lookups, List.append_assoc]

theorem ty_cmp1 : ∀ t < 3, (BitVec.ofNat 32 t - BitVec.ofNat 32 1 == 0) = decide (t = 1) := by decide

/-- `I` of the block `4g + c`, of type `tt`, from the half `D` in `m`. -/
def Iof (tt : Nat) (km kr : BitVec 32) (m : Mem) (W : BitVec 32) (g c : Nat) : BitVec 32 :=
  (Proof.Cast5.mix tt km (dword (m.readW (slot W (rOff g)) 128) c)).rotateLeft (kr.toNat % 32)

/-- `f` of a round, from the entries of the four S-boxes at the bytes of `I`. -/
theorem f_lane {tt r : Nat} (htt : tt = 1 ∨ tt = 2 ∨ tt = 3) (hmod : tt % 3 = (r + 1) % 3) (km kr d : BitVec 32) :
    Proof.Cast5.comb (tt % 3)
      (sboxOf 0 (((Proof.Cast5.mix tt km d).rotateLeft (kr.toNat % 32)).extractLsb' (8 * (3 - 0)) 8))
      (sboxOf 1 (((Proof.Cast5.mix tt km d).rotateLeft (kr.toNat % 32)).extractLsb' (8 * (3 - 1)) 8))
      (sboxOf 2 (((Proof.Cast5.mix tt km d).rotateLeft (kr.toNat % 32)).extractLsb' (8 * (3 - 2)) 8))
      (sboxOf 3 (((Proof.Cast5.mix tt km d).rotateLeft (kr.toNat % 32)).extractLsb' (8 * (3 - 3)) 8)) =
      Spec.Cast5.f (r + 1) d km kr := by
  rw [f_eq, roundI, ← hmod, ← mix_mod htt]
  simp only [Spec.Cast5.byte, shr8]
  rfl

/-- **A round of the sixteen blocks.** -/
theorem round_wp {s₀ : State} {K W : BitVec 32} {k : Schedule} {up : Bool} {n : Nat} (F : Fix16 K W k s₀)
    (hn : n ≤ 16) {i : Nat} (hi : i < n) {u : State} (hI : RInv s₀ K W k up n i u) {cn : BitVec 32}
    (hc : u.mem.readW (slot W cnOff) 32 = cn) :
    WP isa Impl.Cast5.X86.Ssse3.Wide.round u fun u' =>
      RInv s₀ K W k up n (i + 1) u' ∧ u'.mem.readW (slot W cnOff) 32 = cn - 1#32 ∧
        u'.zf = some (cn - 1#32 == 0) := by
  have E := hI.env
  have fW := E.fW
  have fK := E.fK
  obtain ⟨r, hr⟩ : ∃ r, r = rnd up n i := ⟨_, rfl⟩
  have r16 : r < 16 := by have := rnd_lt up hi; omega
  have kAt : ∀ j < 32, u.mem.readW (slot K (4 * j)) 32 = k.getD j 0 := fun j hj =>
    (hI.frame.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact F.dKW) (by decide)).trans (F.key j hj)
  obtain ⟨km, hkm⟩ : ∃ km, km = k.getD r 0 := ⟨_, rfl⟩
  obtain ⟨kr, hkr⟩ : ∃ kr, kr = k.getD (16 + r) 0 := ⟨_, rfl⟩
  obtain ⟨t, htd⟩ : ∃ t, t = (r + 1) % 3 := ⟨_, rfl⟩
  have t3 : t < 3 := by omega
  obtain ⟨ty, tz, -⟩ := tyOf_eq r r16
  rw [← htd] at ty tz
  unfold Impl.Cast5.X86.Ssse3.Wide.round
  refine WP.seq (WP.mono (roundType_wp (km := km) (kr := kr) E r16 (by rw [hr]; exact hI.rn hi)
    ((kAt r (by omega)).trans hkm.symm)
    (by rw [show 4 * r + 64 = 4 * (16 + r) by omega]; exact (kAt _ (by omega)).trans hkr.symm))
    fun v ⟨⟨vb, va, vc, vz, vm, vx⟩, vk, vs⟩ => ?_)
  rw [ty] at vb
  rw [tz] at vz
  have Ev : Env16 K W v := ⟨(vk.gpr .esi (by decide)).trans E.esi,
    by rw [vk.gpr tbr (by decide), vs]; exact E.edx, (vk.gpr .ebp (by decide)).trans E.ebp, fW, fK,
    by rw [vk.wr]; exact E.wrW, by rw [vk.rd, vk.wr]; exact E.rdK⟩
  -- `I` before its rotation
  refine WP.seq (byType_wp t3 vz vb fun v₁ tt htt hmod fu₁ x₁ => ?_)
  have E₁ : Env16 K W v₁ := ⟨by rw [fu₁.gpr]; exact Ev.esi, by rw [fu₁.gpr, fu₁.syms]; exact Ev.edx,
    by rw [fu₁.gpr]; exact Ev.ebp, fW, fK, by rw [fu₁.wr]; exact Ev.wrW, by rw [fu₁.rd, fu₁.wr]; exact Ev.rdK⟩
  rw [← List.append_nil (Impl.Cast5.X86.Ssse3.Wide.mix tt)]
  refine mix_wp (km := km) E₁ htt (by rw [fu₁.gpr]; exact va) fun v₂ st₂ c₂ m₂ x₂ => WP.block_nil ?_
  rw [fu₁.mem, vm] at x₂ m₂
  -- the look-ups
  refine WP.seq ?_
  rw [lookups_eq]
  refine rotate_wp (kr := kr) (by rw [c₂, fu₁.gpr]; exact vc) x₂ fun v₃ st₃ x₃ m₃ => ?_
  have E₃ : Env16 K W v₃ := E₁.stay (st₂.trans st₃)
  have M₃ : v₃.mem = u.mem := m₃.trans m₂
  obtain X₃ : ∀ g < 4, (fun g => v₃.xmm (xr g)) g = L (Iof tt km kr u.mem W g) := fun g hg => x₃ g hg
  show WP isa _ (S v₃ v₃.mem v₃.xmm) _
  rw [M₃]
  refine planes_wp E₃ fun m4 g4 hio hf4 => ?_
  have q0 : ∀ i < 16, byte (m4.readW (slot W (ioOff (3 - 0))) 128) i =
      (Iof tt km kr u.mem W (i / 4) (i % 4)).extractLsb' (8 * (3 - 0)) 8 := fun i hi' =>
    io_q (X := fun g => v₃.xmm (xr g)) hio X₃ rfl hi'
  refine sbox16_wp E₃ (j := 0) (by decide) q0 fun m5 g5 hf5 he0 => ?_
  have q1 : ∀ i < 16, byte (m5.readW (slot W (ioOff (3 - 1))) 128) i =
      (Iof tt km kr u.mem W (i / 4) (i % 4)).extractLsb' (8 * (3 - 1)) 8 := fun i hi' =>
    io_q (X := fun g => v₃.xmm (xr g)) hio X₃
      (sbox_keep (by decide) hf5 (.inr (.inl ⟨by decide, by decide⟩)) (by decide)) hi'
  refine sbox16_wp E₃ (j := 1) (by decide) q1 fun m6 g6 hf6 he1 => ?_
  have q2 : ∀ i < 16, byte (m6.readW (slot W (ioOff (3 - 2))) 128) i =
      (Iof tt km kr u.mem W (i / 4) (i % 4)).extractLsb' (8 * (3 - 2)) 8 := fun i hi' =>
    io_q (X := fun g => v₃.xmm (xr g)) hio X₃
      ((sbox_keep (by decide) hf6 (.inr (.inl ⟨by decide, by decide⟩)) (by decide)).trans
        (sbox_keep (by decide) hf5 (.inr (.inl ⟨by decide, by decide⟩)) (by decide))) hi'
  refine sbox16_wp E₃ (j := 2) (by decide) q2 fun m7 g7 hf7 he2 => ?_
  have q3 : ∀ i < 16, byte (m7.readW (slot W (ioOff (3 - 3))) 128) i =
      (Iof tt km kr u.mem W (i / 4) (i % 4)).extractLsb' (8 * (3 - 3)) 8 := fun i hi' =>
    io_q (X := fun g => v₃.xmm (xr g)) hio X₃
      ((sbox_keep (by decide) hf7 (.inr (.inl ⟨by decide, by decide⟩)) (by decide)).trans
        ((sbox_keep (by decide) hf6 (.inr (.inl ⟨by decide, by decide⟩)) (by decide)).trans
          (sbox_keep (by decide) hf5 (.inr (.inl ⟨by decide, by decide⟩)) (by decide)))) hi'
  refine sbox16_wp E₃ (j := 3) (by decide) q3 fun m8 g8 hf8 he3 => ?_
  -- what the look-ups keep and leave
  obtain kp : ∀ o, o + 16 ≤ 272 → m8.readW (slot W o) 128 = u.mem.readW (slot W o) 128 := fun o ho =>
    (sbox_keep (by decide) hf8 (.inl ho) (by omega)).trans ((sbox_keep (by decide) hf7 (.inl ho) (by omega)).trans
      ((sbox_keep (by decide) hf6 (.inl ho) (by omega)).trans ((sbox_keep (by decide) hf5 (.inl ho) (by omega)).trans
        (keep16 hf4 fun r hr' => by
          rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (by omega) (by omega) (by decide)))))
  obtain en : ∀ j < 4, ∀ g < 4, ∀ c < 4, dword (m8.readW (slot W (enOff j g)) 128) c =
      sboxOf j ((Iof tt km kr u.mem W g c).extractLsb' (8 * (3 - j)) 8) := by
    intro j hj g hg c hc'
    have dm : (4 * g + c) / 4 = g ∧ (4 * g + c) % 4 = c := by omega
    rcases cases4 hj with rfl | rfl | rfl | rfl
    · rw [sbox_keep (by decide) hf8 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega),
        sbox_keep (by decide) hf7 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega),
        sbox_keep (by decide) hf6 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega), he0 g hg c hc', dm.1, dm.2]
    · rw [sbox_keep (by decide) hf8 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega),
        sbox_keep (by decide) hf7 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega), he1 g hg c hc', dm.1, dm.2]
    · rw [sbox_keep (by decide) hf8 (.inr (.inl ⟨by simp only [enOff]; omega, by simp only [enOff]; omega⟩))
          (by simp only [enOff]; omega), he2 g hg c hc', dm.1, dm.2]
    · rw [he3 g hg c hc', dm.1, dm.2]
  obtain sc : ∀ o, 256 ≤ o → o + 4 ≤ 272 → m8.readW (slot W o) 32 = u.mem.readW (slot W o) 32 := by
    intro o h1 h2
    have d2 : ∀ {j : Nat} {ma mb : Mem}, j < 4 → Frame [vR W, enR W j] ma mb →
        mb.readW (slot W o) 32 = ma.readW (slot W o) 32 := fun {j} {ma} {mb} hj hf => keep4 hf fun r hr' => by
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact Offset.disjoint _ (by omega) (by omega) (by decide)
      · rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    exact (d2 (by decide) hf8).trans ((d2 (by decide) hf7).trans ((d2 (by decide) hf6).trans
      ((d2 (by decide) hf5).trans (keep4 hf4 fun r hr' => by
        rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (by omega) (by omega) (by decide)))))
  obtain fr8 : Frame [wR16 W] u.mem m8 := by
    have s2 : ∀ {j : Nat} {ma mb : Mem}, j < 4 → Frame [vR W, enR W j] ma mb → Frame [wR16 W] ma mb :=
      fun {j} {ma} {mb} hj hf => hf.sub fun r hr' => ⟨_, List.mem_cons_self, by
        rcases List.mem_cons.mp hr' with rfl | hr'
        · exact Offset.sub_base _ (by decide)
        · rw [List.mem_singleton.mp hr']; exact Offset.sub_base _ (by omega)⟩
    exact (hf4.sub fun r hr' => ⟨_, List.mem_cons_self, by
      rw [List.mem_singleton.mp hr']; exact Offset.sub_base _ (by decide)⟩).trans
      ((s2 (by decide) hf5).trans ((s2 (by decide) hf6).trans ((s2 (by decide) hf7).trans (s2 (by decide) hf8))))
  -- the type again
  refine wp_cmpix fun v₉ fu₉ z₉ x₉ => WP.block_nil ?_
  obtain G₉ : ∀ q, q ≠ .eax → q ≠ .ecx → v₉.gpr q = v₁.gpr q := fun q a b => by
    rw [fu₉.gpr]; exact (st₂.trans st₃).gpr q a b
  obtain b₉ : v₉.gpr .ebx = BitVec.ofNat 32 t := by
    rw [G₉ _ (by decide) (by decide), fu₁.gpr]; exact vb
  obtain z₉' : v₉.zf = some (decide (t = 1)) := by
    rw [z₉]
    show some (v₃.gpr .ebx - BitVec.ofNat 32 1 == 0) = _
    rw [(st₂.trans st₃).gpr _ (by decide) (by decide), fu₁.gpr, vb, ty_cmp1 t t3]
  refine WP.seq (byType_wp t3 z₉' b₉ fun v₁₀ tt' htt' hmod' fu₁₀ x₁₀ => ?_)
  obtain rfl : tt' = tt := by omega
  obtain G₁₀ : ∀ q, q ≠ .eax → q ≠ .ecx → q ≠ .ebx → v₁₀.gpr q = u.gpr q := fun q a b c => by
    rw [fu₁₀.gpr, G₉ q a b, fu₁.gpr]
    exact vk.gpr q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b, c⟩)
  obtain RD : v₁₀.rd = u.rd := by rw [fu₁₀.rd, fu₉.rd]; exact ((st₂.trans st₃).rd.trans fu₁.rd).trans vk.rd
  obtain WR : v₁₀.wr = u.wr := by rw [fu₁₀.wr, fu₉.wr]; exact ((st₂.trans st₃).wr.trans fu₁.wr).trans vk.wr
  obtain SY : v₁₀.syms = u.syms := by
    rw [fu₁₀.syms, fu₉.syms]; exact ((st₂.trans st₃).syms.trans fu₁.syms).trans vs
  obtain M₁₀ : v₁₀.mem = m8 := fu₁₀.mem.trans fu₉.mem
  have E₁₀ : Env16 K W v₁₀ := ⟨(G₁₀ _ (by decide) (by decide) (by decide)).trans E.esi,
    by rw [G₁₀ tbr (by decide) (by decide) (by decide), SY]; exact E.edx,
    (G₁₀ _ (by decide) (by decide) (by decide)).trans E.ebp, fW, fK, by rw [WR]; exact E.wrW,
    by rw [RD, WR]; exact E.rdK⟩
  rw [← List.append_nil (Impl.Cast5.X86.Ssse3.Wide.comb tt'), comb_eq htt']
  show WP isa _ (S v₁₀ v₁₀.mem v₁₀.xmm) _
  rw [M₁₀]
  refine wp_tbE E₁₀ (by decide) (wp_tbE E₁₀ (by decide) (combs_wp E₁₀ (m₀ := m8) 4 0 m8 _ (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self]) (upd_self _ _ _) (fun g' h => absurd h (Nat.not_lt_zero _))
    (fun g' _ _ => ⟨rfl, rfl⟩) (Same.refl _ _ _ _) (Frame.refl _ _) fun m11 g11 hd hf11 => WP.block_nil ?_))
  -- the next round's number
  have E₁₁ : Env16 K W (S v₁₀ m11 g11) := ⟨E₁₀.esi, E₁₀.edx, E₁₀.ebp, fW, fK, E₁₀.wrW, E₁₀.rdK⟩
  obtain sc11 : ∀ o, 256 ≤ o → o + 4 ≤ 272 → m11.readW (slot W o) 32 = u.mem.readW (slot W o) 32 := fun o h1 h2 =>
    (keep4 hf11 fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact Offset.disjoint _ (by omega) (by omega) (by decide)).trans (sc o h1 h2)
  refine WP.mono (next_wp E₁₁ (rn := BitVec.ofNat 32 r) (st := stv up) (cn := cn)
    ((sc11 _ (by decide) (by decide)).trans (by rw [hr]; exact hI.rn hi))
    ((sc11 _ (by decide) (by decide)).trans hI.st) ((sc11 _ (by decide) (by decide)).trans hc))
    fun w ⟨⟨wz, wm, _⟩, wk, ws⟩ => ?_
  obtain GW : ∀ q, q ≠ .eax → q ≠ .ecx → q ≠ .ebx → w.gpr q = u.gpr q := fun q a b c =>
    (wk.gpr q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b⟩)).trans (G₁₀ q a b c)
  refine ⟨⟨⟨(GW _ (by decide) (by decide) (by decide)).trans E.esi, ?_,
      (GW _ (by decide) (by decide) (by decide)).trans E.ebp, fW, fK, by rw [wk.wr]; exact E₁₀.wrW,
      by rw [wk.rd, wk.wr]; exact E₁₀.rdK⟩,
    (GW _ (by decide) (by decide) (by decide)).trans hI.esp,
    (GW _ (by decide) (by decide) (by decide)).trans hI.edi, (wk.rd.trans RD).trans hI.rd,
    (wk.wr.trans WR).trans hI.wr, (ws.trans SY).trans hI.syms, ?_, fun b hb => ?_, fun h' => ?_, ?_⟩, ?_, wz⟩
  · rw [GW tbr (by decide) (by decide) (by decide), ws]
    show u.gpr tbr = v₁₀.syms tableName
    rw [SY]; exact E.edx
  · rw [wm]
    exact ((((hI.frame.trans fr8).trans (hf11.sub fun r hr' => ⟨_, List.mem_cons_self, by
      rw [List.mem_singleton.mp hr']; exact Offset.sub_base _ (by decide)⟩)).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide) (by decide))).writeW List.mem_cons_self _
      (Offset.contains_base _ (by decide) (by decide)))
  · have g4 : b / 4 < 4 := by omega
    have c4 : b % 4 < 4 := Nat.mod_lt _ (by decide)
    obtain ⟨dl, dr⟩ := hd (b / 4) g4
    rw [fold_succ up k hi, ← hI.hv b hb, ← hr]
    refine Prod.ext ?_ ?_
    · show dword (w.mem.readW (slot W (lOff (b / 4))) 128) (b % 4) =
        dword (u.mem.readW (slot W (rOff (b / 4))) 128) (b % 4)
      rw [wm, rd16_wr4 _ W _ (by simp only [lOff, cnOff]; omega) (by simp only [lOff]; omega) (by decide),
        rd16_wr4 _ W _ (by simp only [lOff, rnOff]; omega) (by simp only [lOff]; omega) (by decide), dl,
        kp _ (by simp only [rOff]; omega)]
    · show dword (w.mem.readW (slot W (rOff (b / 4))) 128) (b % 4) =
        dword (u.mem.readW (slot W (lOff (b / 4))) 128) (b % 4) ^^^
          Spec.Cast5.f (r + 1) (dword (u.mem.readW (slot W (rOff (b / 4))) 128) (b % 4)) (k.getD r 0)
            (k.getD (15 + (r + 1)) 0)
      rw [wm, rd16_wr4 _ W _ (by simp only [rOff, cnOff]; omega) (by simp only [rOff]; omega) (by decide),
        rd16_wr4 _ W _ (by simp only [rOff, rnOff]; omega) (by simp only [rOff]; omega) (by decide), dr _ c4,
        kp _ (by simp only [lOff]; omega),
        show fv (ops tt').1 (ops tt').2.1 (ops tt').2.2 m8 W (b / 4) (b % 4) = _ from fo_comb htt' _ _ _ _,
        en 0 (by decide) _ g4 _ c4, en 1 (by decide) _ g4 _ c4, en 2 (by decide) _ g4 _ c4,
        en 3 (by decide) _ g4 _ c4, show 15 + (r + 1) = 16 + r by omega, ← hkm, ← hkr]
      exact congrArg _ (f_lane htt' (hmod'.trans htd) km kr _)
  · rw [wm, rd4_wr4 _ W _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hr]
    exact rnd_step up hn h'
  · rw [wm, rd4_wr4 _ W _ (by decide) (by decide) (by decide), rd4_wr4 _ W _ (by decide) (by decide) (by decide)]
    exact (sc11 _ (by decide) (by decide)).trans hI.st
  · rw [wm, Mem.readW_writeW_self32]

/-! ## The function -/

open VG.Proof.Cast5.X86 (symFrame_ok' wp_countdownF blockAt_frame cipher cipher_eq)

theorem fold_zero (up : Bool) (k : Schedule) (n : Nat) (lr : BitVec 32 × BitVec 32) : fold up k n 0 lr = lr := by
  cases up <;> rfl

/-- A doubleword of a sixteen-byte place that is the same in two memories. -/
theorem same4 {W : BitVec 32} {lo hi : Nat} {m m' : Mem} (h : Same W lo hi m m') {o j : Nat} (hj : j < 4)
    (h1 : lo ≤ o) (h2 : o + 16 ≤ hi) :
    m'.readW (slot W (o + 4 * j)) 32 = m.readW (slot W (o + 4 * j)) 32 := by
  show m'.readW (W.setWidth 64 + BitVec.ofNat 64 (o + 4 * j)) 32 =
    m.readW (W.setWidth 64 + BitVec.ofNat 64 (o + 4 * j)) 32
  rw [← Offset.add_add, ← dword_readW _ _ hj, ← dword_readW _ _ hj]
  exact congrArg (dword · j) (h o h1 h2)

theorem blocksIn_eq : blocksIn = tb .xmm6 oKL :: tb .xmm7 oKR :: ((List.range' 0 4).flatMap blockIn ++ []) := by
  rw [blocksIn, List.range_eq_range', List.append_nil]; rfl

/-- **The sixteen-block function**: the sixteen blocks at the working space
at `esi`, each through the `n` rounds in the order the working space states,
under the subkeys at `ebp`; it writes the working space's 848 bytes and the
four bytes below `esp`. -/
theorem cryptBlocks_wp {s : State} {K W : BitVec 32} {k : Schedule} {up : Bool} {n : Nat}
    (hW : s.gpr .esi = W) (hK : s.gpr .ebp = K) (fW : W.toNat + 848 ≤ 2 ^ 32) (fK : K.toNat + 128 ≤ 2 ^ 32)
    (wrW : ∀ o n, o + n ≤ 848 → InRegions s.wr (slot W o) n)
    (rdK : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (slot K o) n)
    (dKW : Region.Disjoint ⟨K.setWidth 64, 128⟩ (wR16 W))
    (key : ∀ i < 32, s.mem.readW (slot K (4 * i)) 32 = k.getD i 0) (hsp : 4 ≤ (s.gpr .esp).toNat)
    (dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 4))
    (dWS : Region.Disjoint (wR16 W) (below (s.gpr .esp) 4)) (hn : 0 < n ∧ n ≤ 16)
    (hrn : s.mem.readW (slot W rnOff) 32 = BitVec.ofNat 32 (rnd up n 0))
    (hst : s.mem.readW (slot W stOff) 32 = stv up) (hcn : s.mem.readW (slot W cnOff) 32 = BitVec.ofNat 32 n) :
    WP isa cryptBlocks s fun s' =>
      (∀ b < 16, blockAt s'.mem (slot W (bufOff + 8 * b)) =
        cipher up k n (blockAt s.mem (slot W (bufOff + 8 * b)))) ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [wR16 W, below (s.gpr .esp) 4] s.mem s'.mem := by
  unfold cryptBlocks
  refine WP.seq (WP.mono (symFrame_ok' tableName s hsp) fun s₀ ⟨h₀, x₀⟩ => WP.seq ?_)
  refine wp_movx fun s₁ u₁ x₁ => ?_
  obtain G₁ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ tbr → s₁.gpr r = s.gpr r := fun r a b c =>
    (u₁.other r c).trans (h₀.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨a, b⟩))
  obtain RD : s₁.rd = s.rd := u₁.rd.trans h₀.rd
  obtain WR : s₁.wr = s.wr := u₁.wr.trans h₀.wr
  obtain SY : s₁.syms = s.syms := u₁.syms.trans h₀.syms
  obtain f₁ : Frame [below (s.gpr .esp) 4] s.mem s₁.mem := by rw [u₁.mem]; exact h₀.frame
  have E₁ : Env16 K W s₁ := ⟨(G₁ _ (by decide) (by decide) (by decide)).trans hW,
    by rw [u₁.gpr, h₀.addr, SY], (G₁ _ (by decide) (by decide) (by decide)).trans hK, fW, fK,
    by rw [WR]; exact wrW, by rw [RD, WR]; exact rdK⟩
  obtain k4 : ∀ o, o + 4 ≤ 848 → s₁.mem.readW (slot W o) 32 = s.mem.readW (slot W o) 32 := fun o ho =>
    keep4 f₁ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dWS.sub_left (Offset.sub_base _ ho)
  obtain F : Fix16 K W k s₁ := ⟨dKW, fun i hi =>
    (f₁.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS) (by decide)).trans (key i hi)⟩
  rw [blocksIn_eq]
  show WP isa _ (S s₁ s₁.mem s₁.xmm) _
  refine wp_tbE E₁ (by decide) (wp_tbE E₁ (by decide) (blocksIn_wp E₁ (m₀ := s₁.mem) 4 0 s₁.mem _ (by decide)
    (by rw [upd_ne _ _ (by decide), upd_self]) (upd_self _ _ _) (fun b h => absurd h (Nat.not_lt_zero _))
    (Same.refl _ _ _ _) (Same.refl _ _ _ _) (Frame.refl _ _) fun m2 f2 hh hs2 hf2 => WP.block_nil ?_))
  obtain I₀ : RInv s₁ K W k up n 0 (S s₁ m2 f2) := ⟨⟨E₁.esi, E₁.edx, E₁.ebp, fW, fK, E₁.wrW, E₁.rdK⟩, rfl, rfl, rfl,
    rfl, rfl, hf2, fun b hb => by rw [fold_zero]; exact hh b (by omega),
    fun _ => ((same4 hs2 (o := 256) (j := 0) (by decide) (by decide) (by decide)).trans
      (k4 _ (by decide))).trans hrn,
    ((same4 hs2 (o := 256) (j := 1) (by decide) (by decide) (by decide)).trans (k4 _ (by decide))).trans hst⟩
  refine WP.seq (wp_countdownF (fun s => s.mem.readW (slot W cnOff) 32) (N := n) (by omega) hn.1
    (fun i s => RInv s₁ K W k up n i s) (fun i hi s hI _ => round_wp F hn.2 hi hI rfl) (fun s₃ hI₃ => ?_) I₀
    (((same4 hs2 (o := 256) (j := 2) (by decide) (by decide) (by decide)).trans (k4 _ (by decide))).trans hcn))
  show WP isa _ (S s₃ s₃.mem s₃.xmm) _
  refine blocksOut_wp hI₃.env fun m' g hb hf' => ⟨fun b hb' => ?_,
    (hI₃.env.esi.trans hW.symm), hI₃.edi.trans (G₁ _ (by decide) (by decide) (by decide)),
    hI₃.env.ebp.trans hK.symm, hI₃.esp.trans (G₁ _ (by decide) (by decide) (by decide)), hI₃.rd.trans RD,
    hI₃.wr.trans WR, hI₃.syms.trans SY, ?_⟩
  · rw [hb b hb', hI₃.hv b hb', cipher_eq]
    have e : st0 s₁.mem W b = decodeBlock (blockAt s.mem (slot W (bufOff + 8 * b))) :=
      congrArg decodeBlock (blockAt_frame f₁ fun r hr => by
        rw [List.mem_singleton.mp hr]; exact dWS.sub_left (Offset.sub_base _ (by simp only [bufOff]; omega)))
    rw [e]
    rfl
  · refine (f₁.mono fun r hr => List.mem_cons_of_mem _ hr).trans ?_
    exact ((hI₃.frame.trans (hf'.mono fun r hr => hr)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)

/-! ## The call -/

/-- **The call of the sixteen-block function**, with eight bytes of stack
apart from the subkeys and from the working space. -/
theorem call_wp {s : State} {K W : BitVec 32} {k : Schedule} {up : Bool} {n : Nat}
    (hW : s.gpr .esi = W) (hK : s.gpr .ebp = K) (fW : W.toNat + 848 ≤ 2 ^ 32) (fK : K.toNat + 128 ≤ 2 ^ 32)
    (wrW : ∀ o n, o + n ≤ 848 → InRegions s.wr (slot W o) n)
    (rdK : ∀ o n, o + n ≤ 128 → InRegions (s.rd ++ s.wr) (slot K o) n)
    (dKW : Region.Disjoint ⟨K.setWidth 64, 128⟩ (wR16 W))
    (key : ∀ i < 32, s.mem.readW (slot K (4 * i)) 32 = k.getD i 0) (hsp : 8 ≤ (s.gpr .esp).toNat)
    (dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 8))
    (dWS : Region.Disjoint (wR16 W) (below (s.gpr .esp) 8)) (hn : 0 < n ∧ n ≤ 16)
    (hrn : s.mem.readW (slot W rnOff) 32 = BitVec.ofNat 32 (rnd up n 0))
    (hst : s.mem.readW (slot W stOff) 32 = stv up) (hcn : s.mem.readW (slot W cnOff) 32 = BitVec.ofNat 32 n) :
    WP isa (.call fnName cryptBlocks) s fun s' =>
      (∀ b < 16, blockAt s'.mem (slot W (bufOff + 8 * b)) =
        cipher up k n (blockAt s.mem (slot W (bufOff + 8 * b)))) ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .ebp = s.gpr .ebp ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.syms = s.syms ∧
      Frame [wR16 W, below (s.gpr .esp) 8] s.mem s'.mem := by
  obtain ⟨r4, r8, d48⟩ := call_regions hsp
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  obtain k4 : ∀ o, o + 4 ≤ 848 → s.callEntry.mem.readW (slot W o) 32 = s.mem.readW (slot W o) 32 := fun o ho =>
    keep4 fc fun r hr => by rw [List.mem_singleton.mp hr]; exact dWS.sub_left (Offset.sub_base _ ho)
  refine WP.callBody (WP.mono (cryptBlocks_wp (s := s.callEntry) (k := k) (up := up) (n := n)
      ((State.callEntry_gpr s (by decide)).trans hW) ((State.callEntry_gpr s (by decide)).trans hK) fW fK wrW rdK
      dKW (fun i hi => (fc.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS) (by decide)).trans (key i hi))
      (by rw [esp', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega)
      (by rw [esp']; exact dKS.sub_right r8) (by rw [esp']; exact dWS.sub_right r8) hn
      ((k4 _ (by decide)).trans hrn) ((k4 _ (by decide)).trans hst) ((k4 _ (by decide)).trans hcn))
    fun u ⟨hres, hsi, hdi, hbp, hesp, hrd, hwr, hsy, hfr⟩ => ⟨?_, ?_, ?_⟩)
  · exact hesp.trans esp'
  · rw [esp'] at hfr
    rw [hfr.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dWS.sub_right r4).symm
      · rw [List.mem_singleton.mp hr]; exact d48
  · obtain U := Upd.setReg u .esp (s.gpr .esp)
    refine ⟨fun b hb => ?_, ((U.other _ (by decide)).trans hsi).trans (State.callEntry_gpr s (by decide)),
      ((U.other _ (by decide)).trans hdi).trans (State.callEntry_gpr s (by decide)),
      ((U.other _ (by decide)).trans hbp).trans (State.callEntry_gpr s (by decide)), U.gpr, U.rd.trans hrd,
      U.wr.trans hwr, U.syms.trans hsy, ?_⟩
    · rw [U.mem, hres b hb, blockAt_frame fc fun r hr => by
        rw [List.mem_singleton.mp hr]; exact dWS.sub_left (Offset.sub_base _ (by simp only [bufOff]; omega))]
    · rw [U.mem]
      refine (fc.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self).trans
        (hfr.sub fun r hr => ?_)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr, esp']
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, r8⟩

/-! ## The modes' core -/

open VG.Proof.Modes.X86 (ScrIn coreRegion blkAddr blkRegion slotA stkRegion CoreSpec)
open VG.Proof.Cast5.X86.Mode (Base KeyArgs Ready keyR argR stk keyArgs_congr ready_frame dirCipher_bytes addr8
  inRegions_prefix)
open VG.Proof.Cast5 (dirCipher dirCipher_length bytesAt_eq)
open VG.Impl.Modes.X86 (sb)

/-- **The call, as the cipher of the core's sixteen blocks**: from the state
`s₈` after the setup, which differs from the core's state `s` in the three
slots of the rounds' order. -/
theorem crypt_tail {up : Bool} {s s₈ : State} {B K : BitVec 32} {k : Schedule} {n : Nat} (hs : ScrIn s B 222)
    (hb : Base false 8 s K k n) (hsd : (stk 8 s).Disjoint ⟨B.setWidth 64, 888⟩) (hsi : s₈.gpr .esi = B)
    (hbp : s₈.gpr .ebp = K) (hdi : s₈.gpr .edi = B) (hesp : s₈.gpr .esp = s.gpr .esp) (hrd : s₈.rd = s.rd)
    (hwr : s₈.wr = s.wr) (hsy : s₈.syms = s.syms)
    (hm : s₈.mem = ((s.mem.writeW (slot B cnOff) (BitVec.ofNat 32 n)).writeW (slot B rnOff)
      (BitVec.ofNat 32 (rnd up n 0))).writeW (slot B stOff) (stv up)) :
    WP isa (.call fnName cryptBlocks) s₈ fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Ready false 8 888 s' B (k, n) ∧
      Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem s'.mem ∧
      (∀ j < 16, Spec.Aes.bytesAt s'.mem (blkAddr (core16 up) B j) 8 =
        dirCipher up k n (Spec.Aes.bytesAt s.mem (blkAddr (core16 up) B j) 8)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw : (⟨B.setWidth 64, 888⟩ : Region) ∈ s.wr := hs.wr
  have hfB : B.toNat + 888 ≤ 2 ^ 32 := hs.fit
  obtain ⟨dKB, dAB⟩ := hb.dW _ hw
  have hfK := hb.fitK
  have hn : 0 < n ∧ n ≤ 16 := by rcases hb.nv with h | h <;> omega
  obtain cS : ∀ o, 256 ≤ o → o + 4 ≤ 268 → (⟨slot B 256, 12⟩ : Region).Contains (slot B o) (32 / 8) :=
    fun o h h' => Offset.contains _ h (by omega) (by decide)
  obtain f₈ : Frame [⟨slot B 256, 12⟩] s.mem s₈.mem := by
    rw [hm]
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (cS cnOff (by decide) (by decide))).writeW
      List.mem_cons_self _ (cS rnOff (by decide) (by decide))).writeW List.mem_cons_self _
      (cS stOff (by decide) (by decide))
  obtain wSub : Region.Sub (wR16 B) ⟨B.setWidth 64, 888⟩ := Region.sub_prefix (by decide)
  obtain f₈' : Frame [wR16 B] s.mem s₈.mem := f₈.sub fun r hr => ⟨_, List.mem_cons_self, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩
  refine WP.mono (call_wp (k := k) (up := up) (n := n) hsi hbp (by omega) hfK
    (fun o n h => by rw [hwr]; exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun o n h => by rw [hrd, hwr]; exact CallLay.inRegions_sub hb.inK h (by decide))
    (dKB.sub_right wSub)
    (fun i hi => (f₈'.readW (r := ⟨K.setWidth 64, 128⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact dKB.sub_right wSub) (by decide)).trans (by
        rw [← hb.sk, Proof.Cast5.scheduleAt_getD _ _ hi]))
    (by rw [hesp]; exact hb.sp) (by rw [hesp]; exact hb.dKs) (by rw [hesp]; exact (hsd.sub_right wSub).symm) hn
    (by rw [hm, rd4_wr4 _ B _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32])
    (by rw [hm, Mem.readW_writeW_self32])
    (by rw [hm, rd4_wr4 _ B _ (by decide) (by decide) (by decide),
      rd4_wr4 _ B _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]))
    fun s' ⟨hres, _, hdi', _, hesp', hrd', hwr', hsy', hfr⟩ => ?_
  obtain espw : s'.gpr .esp = s.gpr .esp := hesp'.trans hesp
  obtain fall : Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem s'.mem := by
    refine (f₈'.sub fun r hr => ⟨_, List.mem_cons_self, by rw [List.mem_singleton.mp hr]; exact fun _ h => h⟩).trans
      (hfr.sub fun r hr => ?_)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · rw [List.mem_singleton.mp hr, hesp]
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  obtain dAll : ∀ r ∈ [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8],
      (keyR K).Disjoint r ∧ (false = true → (Mode.tabR s).Disjoint r) ∧ (argR s).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨dKB.sub_right wSub, (fun h => nomatch h), dAB.sub_right wSub⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨hb.dKs, (fun h => nomatch h), hb.dAs⟩
  refine ⟨hdi'.trans hdi, espw, ⟨K, hb.frame espw (hrd'.trans hrd) (hwr'.trans hwr) (hsy'.trans hsy) fall dAll,
    by simp only [stk, espw]; exact hsd⟩, fall, fun j hj => ?_, hrd'.trans hrd, hwr'.trans hwr⟩
  have eA : blkAddr (core16 up) B j = slot B (bufOff + 8 * j) := by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 0) + BitVec.ofNat 64 (4 * 2 * j) =
      B.setWidth 64 + BitVec.ofNat 64 (0 + 8 * j)
    rw [Offset.add_add]
  rw [eA, bytesAt_eq, hres j hj, dirCipher_bytes, blockAt_frame f₈ fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)
      (by decide)]

/-- **The sixteen blocks of the core's buffer, encrypted (`up`) or decrypted
in place.** -/
theorem crypt_wp (up : Bool) {s : State} {B : BitVec 32} {kn : Schedule × Nat} (hB : s.gpr sb = B)
    (hs : ScrIn s B 222) (hr : Ready false 8 888 s B kn) :
    WP isa (crypt up) s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready false 8 888 s' B kn ∧
      Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem s'.mem ∧
      (∀ j < 16, Spec.Aes.bytesAt s'.mem (blkAddr (core16 up) B j) 8 =
        dirCipher up kn.1 kn.2 (Spec.Aes.bytesAt s.mem (blkAddr (core16 up) B j) 8)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨k, n⟩ := kn
  obtain ⟨K, hb, hsd⟩ := hr
  have hw : (⟨B.setWidth 64, 888⟩ : Region) ∈ s.wr := hs.wr
  have hfB : B.toNat + 888 ≤ 2 ^ 32 := hs.fit
  have hB' : s.gpr .edi = B := hB
  obtain aE4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := inRegions_prefix hb.inA (by decide)
  obtain aE8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [addr8 hb.fitE]; exact CallLay.inRegions_sub hb.inA (by decide) (by decide)
  obtain aB : ∀ e, e < 888 → addr B e = slot B e := fun e he => addr_eq (by omega)
  obtain sW : ∀ e, e + 4 ≤ 888 → InRegions s.wr (addr B e) 4 := fun e he => by
    rw [aB e (by omega)]; exact ⟨_, hw, Offset.contains_base _ he (by omega)⟩
  refine WP.seq ?_
  show WP isa (.block (.mov .esi (.reg .edi) :: .mov .ebp (.mem ⟨.esp, 4⟩) :: .mov .eax (.mem ⟨.esp, 8⟩) ::
    .store ⟨.esi, cnOff⟩ .eax :: (if up then
      [.mov .eax (imm 0), .store ⟨.esi, rnOff⟩ .eax, .mov .eax (imm 1), .store ⟨.esi, stOff⟩ .eax]
     else [.alu .sub .eax (imm 1), .store ⟨.esi, rnOff⟩ .eax, .mov .eax (imm 0xFFFFFFFF),
       .store ⟨.esi, stOff⟩ .eax]))) s _
  refine wp_mov fun s₁ u₁ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 4) (u₁.other _ (by decide)) (by rw [u₁.rd, u₁.wr]; exact aE4)
    fun s₂ u₂ => ?_
  refine wp_ldm (b := .esp) (B := s.gpr .esp) (o := 8)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact aE8)
    fun s₃ u₃ => ?_
  obtain si₃ : s₃.gpr .esi = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact hB'
  obtain ax₃ : s₃.gpr .eax = BitVec.ofNat 32 n := by rw [u₃.gpr, u₂.mem, u₁.mem]; exact hb.argN
  refine wp_stm (b := .esi) (B := B) (o := cnOff) si₃ (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sW _ (by decide))
    fun s₄ u₄ => ?_
  obtain G₄ : ∀ r, r ≠ .esi → r ≠ .ebp → r ≠ .eax → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [u₄.gpr, u₃.other r c, u₂.other r b, u₁.other r a]
  obtain bp₄ : s₄.gpr .ebp = K := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact hb.argK
  obtain RD₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain WR₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain SY₄ : s₄.syms = s.syms := by rw [u₄.syms, u₃.syms, u₂.syms, u₁.syms]
  obtain M₄ : s₄.mem = s.mem.writeW (slot B cnOff) (BitVec.ofNat 32 n) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, ax₃, aB _ (by decide)]
  obtain si₄ : s₄.gpr .esi = B := by rw [u₄.gpr]; exact si₃
  cases up with
  | true =>
    show WP isa (.block [.mov .eax (imm 0), .store ⟨.esi, rnOff⟩ .eax, .mov .eax (imm 1),
      .store ⟨.esi, stOff⟩ .eax]) s₄ _
    refine wp_movi fun s₅ u₅ => wp_stm (b := .esi) (B := B) (o := rnOff)
      ((u₅.other _ (by decide)).trans si₄) (by rw [u₅.wr, WR₄]; exact sW _ (by decide)) fun s₆ u₆ =>
      wp_movi fun s₇ u₇ => wp_stm (b := .esi) (B := B) (o := stOff)
      (by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide)]; exact si₄)
      (by rw [u₇.wr, u₆.wr, u₅.wr, WR₄]; exact sW _ (by decide)) fun s₈ u₈ => WP.block_nil ?_
    obtain G₈ : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r a => by
      rw [u₈.gpr, u₇.other r a, u₆.gpr, u₅.other r a]
    refine crypt_tail (up := true) hs hb hsd ((G₈ _ (by decide)).trans si₄) ((G₈ _ (by decide)).trans bp₄)
      (((G₈ _ (by decide)).trans (G₄ _ (by decide) (by decide) (by decide))).trans hB')
      ((G₈ _ (by decide)).trans (G₄ _ (by decide) (by decide) (by decide)))
      (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, RD₄]) (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, WR₄])
      (by rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, SY₄]) ?_
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, M₄, u₇.gpr, u₅.gpr, aB _ (by decide), aB _ (by decide)]
    rfl
  | false =>
    show WP isa (.block [.alu .sub .eax (imm 1), .store ⟨.esi, rnOff⟩ .eax, .mov .eax (imm 0xFFFFFFFF),
      .store ⟨.esi, stOff⟩ .eax]) s₄ _
    refine wp_subi fun s₅ u₅ _ _ => wp_stm (b := .esi) (B := B) (o := rnOff)
      ((u₅.other _ (by decide)).trans si₄) (by rw [u₅.wr, WR₄]; exact sW _ (by decide)) fun s₆ u₆ =>
      wp_movi fun s₇ u₇ => wp_stm (b := .esi) (B := B) (o := stOff)
      (by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide)]; exact si₄)
      (by rw [u₇.wr, u₆.wr, u₅.wr, WR₄]; exact sW _ (by decide)) fun s₈ u₈ => WP.block_nil ?_
    obtain G₈ : ∀ r, r ≠ .eax → s₈.gpr r = s₄.gpr r := fun r a => by
      rw [u₈.gpr, u₇.other r a, u₆.gpr, u₅.other r a]
    have hn : n = 12 ∨ n = 16 := hb.nv
    refine crypt_tail (up := false) hs hb hsd ((G₈ _ (by decide)).trans si₄) ((G₈ _ (by decide)).trans bp₄)
      (((G₈ _ (by decide)).trans (G₄ _ (by decide) (by decide) (by decide))).trans hB')
      ((G₈ _ (by decide)).trans (G₄ _ (by decide) (by decide) (by decide)))
      (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, RD₄]) (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, WR₄])
      (by rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, SY₄]) ?_
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, M₄, u₇.gpr, u₅.gpr, u₄.gpr, ax₃, aB _ (by decide), aB _ (by decide)]
    rcases hn with rfl | rfl <;> rfl

/-- **The sixteen-block core by `pshufb` meets what the modes need**, in
either direction, with nothing to prepare. -/
def coreSpec16 (up : Bool) : CoreSpec (core16 up) where
  Key := Schedule × Nat
  cipher kn := dirCipher up kn.1 kn.2
  KeyArgs := KeyArgs false 8
  Ready := Ready false 8 888
  cipher_len kn b := dirCipher_length up kn.1 kn.2 b
  layout := ⟨show 0 < 16 by decide, .inl rfl, show 0 + 2 * 16 ≤ 212 by decide, show 212 + 10 ≤ 222 by decide⟩
  keyArgs_congr := keyArgs_congr
  ready_frame h hesp hrd hwr hsy hf hsub _ := ready_frame h hesp hrd hwr hsy hf hsub
  prepare_wp hB _ hR hk _ := by
    obtain ⟨K, hb, hd⟩ := hk
    exact WP.block_nil ⟨⟨K, hb, (hd _ hR).2.2.2⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp := fun {s B kn} hB hs hr _ => crypt_wp up hB hs hr

/-- It fits CAST5's functions: no table in memory, 888 bytes of working
space and eight bytes of stack. -/
def fits16 (up : Bool) : ModeFns.Fits (coreSpec16 up) false 888 8 where
  toKey := id
  keyArgs h := h
  bw := rfl
  ka := rfl
  stack := rfl
  total := rfl

end VG.Proof.Cast5.X86.Ssse3.Wide
