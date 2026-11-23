module

public import VerifiedGarbage.Impl.Blowfish.X86.Ssse3Wide
public import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Core
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseLanes
import VerifiedGarbage.Proof.Framework.X86.ByteMap
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Blowfish.Blocks

-- separate module: the sixteen-block function's proof, which the functions' checks (`Ssse3WideVerified.lean`) do
-- not change with

/-!
# Blowfish's sixteen-block function by `pshufb` on x86 (32-bit): what it computes

The code of `Impl/Blowfish/X86/Ssse3Wide.lean`, with the row step, the
S-box's sixteen rows and the index vectors of one block
(`Ssse3Core.lean`: the code is the same):

* the working space's sixteen-byte places, read through the stores at
  other places (`rd_wr`, `Same`);
* `planesX_wp`: xL after the round's entry of P, and the four registers of
  its bytes; `sboxF_wp`, `sboxL_wp`: an S-box's entries of the sixteen
  blocks, into F, and with the last S-box into the new xL; `round_wp`: a
  round, `roundStep` of each block (`Proof/Blowfish/F.lean`), with the
  entries of P read in the order of use through a pointer;
* `blocksIn_wp`, `blocksOutX_wp`: the blocks' bytes to their halves and
  back; `cryptBlocks_wp`: the function, `feistel` of each of the sixteen
  blocks for the order of the entries of P at its pointer; `call_wp`;
* `crypt_wp`: the modes' core, which gives the function the schedule's P
  to encrypt and a copy of it in reverse, written to the working space
  (`revPs_wp`), to decrypt; `wideCoreSpec up`, `wideFits up`: it meets
  what the modes need, with 111 words of working space and eight bytes of
  stack.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86.Ssse3.Wide

open VG VG.X86 VG.X86.ByteLookup
open VG.Impl.Blowfish.X86 (at_ imm planeOff pOff)
open VG.Impl.Blowfish.X86.Ssse3 (tb x ld stx xr index scan oC oT oM oKL oKR oBS vOff fOff tableName table tbr)
open VG.Impl.Blowfish.X86.Ssse3.Wide
open VG.Proof.MlDsa.X86.Pack (addr_of_fit)
open VG.Spec.Blowfish (Schedule scheduleAt sEntry pEntry)
open VG.Proof.Blowfish (sEntry_byte word_ext pEntry_read scheduleAt_eq_of_frame)
open VG.X86.ByteMap (byte_eq_dword)

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

/-- Where the sixteen-block function runs: as for one block (`Env`), with
the working space's bytes 64 to 767 writable, and the eighteen entries of P
readable at `P`. -/
structure Env16 (K W P : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = K
  edi : s.gpr .edi = W
  ebx : s.gpr tbr = s.syms tableName
  fK : K.toNat + 4168 ≤ 2 ^ 32
  fW : W.toNat + 768 ≤ 2 ^ 32
  fP : P.toNat + 72 ≤ 2 ^ 32
  rdK : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (slot K o) n
  wrW : ∀ o n, 64 ≤ o → o + n ≤ 768 → InRegions s.wr (slot W o) n
  rdP : ∀ o n, o + n ≤ 72 → InRegions (s.rd ++ s.wr) (slot P o) n

theorem Env16.env {K W P : BitVec 32} (E : Env16 K W P s) : Env K W s :=
  ⟨E.esi, E.edi, E.ebx, E.fK, by have := E.fW; omega, E.rdK, fun o n h h' => E.wrW o n h (by omega)⟩

theorem Env16.rdW {K W P : BitVec 32} (E : Env16 K W P s) {o n : Nat} (h : 64 ≤ o) (h' : o + n ≤ 768) :
    InRegions (s.rd ++ s.wr) (slot W o) n := by
  obtain ⟨r, hr, hc⟩ := E.wrW o n h h'
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- A load from the working space. -/
theorem wp_ldW {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {d : XReg} {o : Nat} (ho : 64 ≤ o) (ho' : o + 16 ≤ 768)
    (k : WP isa (.block is) (S s m (upd f d (m.readW (slot W o) 128))) Q) :
    WP isa (.block (ld d .edi o :: is)) (S s m f) Q :=
  wp_ld (ea_at E.edi (by have := E.fW; omega)) (E.rdW ho ho') k

/-- A store to the working space. -/
theorem wp_stW {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {r : XReg} {o : Nat} (ho : 64 ≤ o) (ho' : o + 16 ≤ 768)
    (k : WP isa (.block is) (S s (m.writeW (slot W o) (f r)) f) Q) :
    WP isa (.block (stx .edi o r :: is)) (S s m f) Q :=
  wp_st (ea_at E.edi (by have := E.fW; omega)) (E.wrW _ _ ho ho') k

/-- A constant. -/
theorem wp_tbE {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {d : XReg} {off : Nat} (ho : off % 8 = 0 ∧ off / 8 + 2 ≤ table.length)
    (k : WP isa (.block is) (S s m (upd f d (cst off))) Q) : WP isa (.block (tb d off :: is)) (S s m f) Q :=
  wp_tb E.ebx ho k

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

/-! ## xL after the entry of P, and its bytes -/

/-- The working space's bytes that the sixteen-block function writes. -/
abbrev wR16 (W : BitVec 32) : Region := ⟨slot W 64, 704⟩

theorem wR16_contains (W : BitVec 32) {o : Nat} (h : 64 ≤ o) (h' : o + 16 ≤ 768) :
    (wR16 W).Contains (slot W o) (128 / 8) := Offset.contains _ h (by omega) (by decide)

/-- xL of the blocks `4g` to `4g + 3` in `m₀`, exclusive-ored with `pv`. -/
abbrev tv (m₀ : Mem) (W : BitVec 32) (pv : BitVec 128) (g : Nat) : BitVec 128 :=
  XBinOp.eval .pxor (m₀.readW (slot W (xlOff g)) 128) pv

theorem xorP_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    {g : Nat} (hg : g < 4)
    (k : ∀ f', f' (xr g) = XBinOp.eval .pshufb (tv m W (f .xmm4) g) (f .xmm5) → (∀ q, q ≠ xr g → f' q = f q) →
      WP isa (.block is) (S s (m.writeW (slot W (tOff g)) (tv m W (f .xmm4) g)) f') Q) :
    WP isa (.block (xorP g ++ is)) (S s m f) Q := by
  have h4 : (.xmm4 : XReg) ≠ xr g := by rw [show (.xmm4 : XReg) = xr 4 from rfl]; exact xr_ne (by omega)
  have h5 : (.xmm5 : XReg) ≠ xr g := by rw [show (.xmm5 : XReg) = xr 5 from rfl]; exact xr_ne (by omega)
  show WP isa (.block (ld (xr g) .edi (xlOff g) :: x .pxor (xr g) .xmm4 :: stx .edi (tOff g) (xr g) ::
    x .pshufb (xr g) .xmm5 :: is)) _ _
  refine wp_ldW E (by simp only [xlOff]; omega) (by simp only [xlOff]; omega) (wp_bin (wp_stW E
    (by simp only [tOff]; omega) (by simp only [tOff]; omega) (wp_bin ?_)))
  simp only [upd_self, upd_ne _ _ h4, upd_ne _ _ h5]
  exact k _ (upd_self _ _ _) fun q hq => by rw [upd_ne _ _ hq, upd_ne _ _ hq, upd_ne _ _ hq]

/-- xL of the groups `g` to `g + n - 1` after the entry of P (`pv`, in
`xmm4`), to its places, and their bytes gathered (by `tt`, in `xmm5`), in
the groups' registers. -/
theorem xorPs_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop} {pv tt : BitVec 128}
    {m₀ : Mem} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 → f .xmm4 = pv → f .xmm5 = tt →
      (∀ g' < g, f (xr g') = XBinOp.eval .pshufb (tv m₀ W pv g') tt) →
      (∀ g' < g, m.readW (slot W (tOff g')) 128 = tv m₀ W pv g') → Same W 64 640 m₀ m → Frame [wR16 W] m₀ m →
      (∀ m' f', (∀ g' < g + n, f' (xr g') = XBinOp.eval .pshufb (tv m₀ W pv g') tt) →
        (∀ g' < g + n, m'.readW (slot W (tOff g')) 128 = tv m₀ W pv g') → Same W 64 640 m₀ m' →
        Frame [wR16 W] m₀ m' → WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap xorP ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ hx hm hs hf k => k m f hx hm hs hf
  | succ n ih =>
    intro g m f hn h4 h5 hx hm hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine xorP_wp E (by omega) fun f' e o => ?_
    have x4 : (.xmm4 : XReg) ≠ xr g := by rw [show (.xmm4 : XReg) = xr 4 from rfl]; exact xr_ne (by omega)
    have x5 : (.xmm5 : XReg) ≠ xr g := by rw [show (.xmm5 : XReg) = xr 5 from rfl]; exact xr_ne (by omega)
    obtain em : tv m W (f .xmm4) g = tv m₀ W pv g := by
      rw [tv, hs _ (by simp only [xlOff]; omega) (by simp only [xlOff]; omega), h4]
    rw [em] at e ⊢
    rw [h5] at e
    refine ih (g + 1) _ f' (by omega) ((o _ x4).trans h4) ((o _ x5).trans h5) (fun g' hg' => ?_) (fun g' hg' => ?_)
      (hs.write _ (.inr (by simp only [tOff]; omega)) (by decide) (by simp only [tOff]; omega))
      (hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [tOff]; omega) (by simp only [tOff]; omega)))
      fun m' f'' hx' hm' hs' hf' => k m' f'' (fun g' hg' => hx' g' (by omega)) (fun g' hg' => hm' g' (by omega)) hs' hf'
    · by_cases e' : g' = g
      · rw [e']; exact e
      · rw [o _ (xr_ne (by omega))]; exact hx g' (by omega)
    · by_cases e' : g' = g
      · rw [e']; exact readW_self128 _ _ _
      · exact (rd_wr m W _ (by simp only [tOff]; omega) (by simp only [tOff]; omega)
          (by simp only [tOff]; omega)).trans (hm g' (by omega))

/-- The four registers of the bytes of the sixteen xL after the entry of P. -/
abbrev iov (m₀ : Mem) (W : BitVec 32) (pv : BitVec 128) (b : Nat) : BitVec 128 :=
  tr (XBinOp.eval .pshufb (tv m₀ W pv 0) (cst oT)) (XBinOp.eval .pshufb (tv m₀ W pv 1) (cst oT))
    (XBinOp.eval .pshufb (tv m₀ W pv 2) (cst oT)) (XBinOp.eval .pshufb (tv m₀ W pv 3) (cst oT)) b

/-- `planes` after its load of the entry of P. -/
def planesX : List Instr :=
  ([.xop (.movd .xmm4 .eax), .xop (.pshufd .xmm4 .xmm4 0), tb .xmm5 oT] : List Instr) ++
    ((List.range' 0 4).flatMap xorP ++ (transpose .xmm0 .xmm1 .xmm2 .xmm3 .xmm4 .xmm5 .xmm6 .xmm7 ++
      ([stx .edi (ioOff 0) .xmm0, stx .edi (ioOff 1) .xmm6, stx .edi (ioOff 2) .xmm4, stx .edi (ioOff 3) .xmm7] :
        List Instr)))

theorem planes_eq : planes = .mov .eax (.mem (at_ .edx 0)) :: planesX := by
  rw [planes, planesX, List.range_eq_range']
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- **xL after the entry of P** (in `eax`), at its places, and the four
registers of its bytes at theirs; the other places kept. -/
theorem planesX_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ m' g, (∀ g' < 4, m'.readW (slot W (tOff g')) 128 = tv m W (bc (s.gpr .eax)) g') →
      (∀ b < 4, m'.readW (slot W (ioOff b)) 128 = iov m W (bc (s.gpr .eax)) b) → Same W 64 640 m m' →
      Frame [wR16 W] m m' → WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (planesX ++ is)) (S s m f) Q := by
  rw [planesX]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_xs rfl (wp_xs rfl (wp_tbE E (by decide) (xorPs_wp E (m₀ := m) (pv := bc (s.gpr .eax)) (tt := cst oT)
    4 0 m _ (by decide) rfl rfl (fun g' h => absurd h (Nat.not_lt_zero _)) (fun g' h => absurd h (Nat.not_lt_zero _))
    (Same.refl _ _ _ _) (Frame.refl _ _) fun m1 f1 hx hm hs hf => ?_)))
  have x0 : f1 .xmm0 = _ := hx 0 (by decide)
  have x1 : f1 .xmm1 = _ := hx 1 (by decide)
  have x2 : f1 .xmm2 = _ := hx 2 (by decide)
  have x3 : f1 .xmm3 = _ := hx 3 (by decide)
  refine transpose0_wp fun f2 r0 r1 r2 r3 => wp_stW E (by decide) (by decide) (wp_stW E (by decide) (by decide)
    (wp_stW E (by decide) (by decide) (wp_stW E (by decide) (by decide) ?_)))
  rw [r0, r1, r2, r3, x0, x1, x2, x3]
  refine k _ _ (fun g' hg' => ?_) (fun b hb => ?_)
    ((((hs.write _ (.inr (by decide)) (by decide) (by decide)).write _ (.inr (by decide)) (by decide)
      (by decide)).write _ (.inr (by decide)) (by decide) (by decide)).write _ (.inr (by decide)) (by decide)
      (by decide))
    ((((hf.writeW List.mem_cons_self _ (wR16_contains W (by decide) (by decide))).writeW List.mem_cons_self _
      (wR16_contains W (by decide) (by decide))).writeW List.mem_cons_self _
      (wR16_contains W (by decide) (by decide))).writeW List.mem_cons_self _
      (wR16_contains W (by decide) (by decide)))
  · rw [rd_wr _ W _ (by simp only [tOff, ioOff]; omega) (by simp only [tOff]; omega) (by decide),
      rd_wr _ W _ (by simp only [tOff, ioOff]; omega) (by simp only [tOff]; omega) (by decide),
      rd_wr _ W _ (by simp only [tOff, ioOff]; omega) (by simp only [tOff]; omega) (by decide),
      rd_wr _ W _ (by simp only [tOff, ioOff]; omega) (by simp only [tOff]; omega) (by decide)]
    exact hm g' hg'
  · rcases cases4 hb with rfl | rfl | rfl | rfl
    · rw [rd_wr _ W _ (by decide) (by decide) (by decide), rd_wr _ W _ (by decide) (by decide) (by decide),
        rd_wr _ W _ (by decide) (by decide) (by decide), readW_self128]
    · rw [rd_wr _ W _ (by decide) (by decide) (by decide), rd_wr _ W _ (by decide) (by decide) (by decide),
        readW_self128]
    · rw [rd_wr _ W _ (by decide) (by decide) (by decide), readW_self128]
    · rw [readW_self128]

/-! ## An S-box of the sixteen blocks -/

open VG.Proof.Blowfish (quarter sq fAcc fAcc_three)

theorem rw_ne : ∀ g < 4, ∀ g' < 4, g ≠ g' → rw g ≠ rw g' := by decide

theorem rw_ne5 : ∀ g < 4, rw g ≠ .xmm5 := by decide

theorem rw_ne6 : ∀ g < 4, rw g ≠ .xmm6 := by decide

/-- The four registers of an S-box's entries, each shuffled by `T`. -/
theorem shuf4_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ g, (∀ gI < 4, g (rw gI) = XBinOp.eval .pshufb (f (rw gI)) (cst oT)) → WP isa (.block is) (S s m g) Q) :
    WP isa (.block (tb .xmm5 oT :: x .pshufb .xmm4 .xmm5 :: x .pshufb .xmm2 .xmm5 :: x .pshufb .xmm0 .xmm5 ::
      x .pshufb .xmm3 .xmm5 :: is)) (S s m f) Q :=
  wp_tbE E (by decide) (wp_bin (wp_bin (wp_bin (wp_bin (k _ fun gI h => by
    rcases cases4 h with rfl | rfl | rfl | rfl <;> rfl)))))

/-- **An S-box's entries of the sixteen blocks**: with byte `3 - j` of the
sixteen xL (`t`) at its place, the entries of S-box `j` at them, four a
register; only the index vectors' places change. -/
theorem front_wp {K W P : BitVec 32} (E : Env16 K W P s) (dKV : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (vR W))
    {t : Nat → BitVec 32} {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j : Nat} (hj : j < 4)
    (hIO : ∀ i < 16, byte (m.readW (slot W (ioOff (3 - j))) 128) i = quarter (t i) j)
    (k : ∀ m' g, Frame [vR W] m m' →
      (∀ gI < 4, ∀ k < 4, dword (g (rw gI)) k = sq (scheduleAt m (K.setWidth 64)) (t (4 * gI + k)) j) →
      WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (Impl.Blowfish.X86.Ssse3.Wide.nibbles j ++ ((List.range' 0 16).flatMap index ++
      (scan j ++ (entries ++ is))))) (S s m f) Q := by
  show WP isa (.block (ld .xmm0 .edi (ioOff (3 - j)) :: tb .xmm2 oM :: x .movdqa .xmm1 .xmm0 ::
    .xop (.shift .psrld .xmm1 4) :: x .pand .xmm1 .xmm2 :: x .pand .xmm0 .xmm2 ::
    ((List.range' 0 16).flatMap index ++ (scan j ++ (entries ++ is))))) _ _
  refine wp_ldW E (by simp only [ioOff]; omega) (by simp only [ioOff]; omega) (wp_tbE E (by decide) (wp_bin
    (wp_xs rfl (wp_bin (wp_bin (indexes_wp E.env (m₀ := m)
      (H := XBinOp.eval .pand (XShiftOp.eval .psrld (m.readW (slot W (ioOff (3 - j))) 128) 4) (cst oM))
      (L := XBinOp.eval .pand (m.readW (slot W (ioOff (3 - j))) 128) (cst oM)) 16 0 m _ (by decide) rfl rfl
      (fun r' h => absurd h (Nat.not_lt_zero _)) (Frame.refl _ _) fun m1 f1 hV hf1 =>
    scan_wp E.env hj fun f2 hA => transpose4_wp fun f3 r0 r1 r2 r3 => shuf4_wp E fun f4 h4 =>
    k _ _ hf1 fun gI hgI c hc => ?_))))))
  obtain hS : scheduleAt m1 (K.setWidth 64) = scheduleAt m (K.setWidth 64) :=
    scheduleAt_eq_of_frame _ hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact dKV
  have a4 : f2 .xmm4 = _ := hA 0 (by decide)
  have a5 : f2 .xmm5 = _ := hA 1 (by decide)
  have a6 : f2 .xmm6 = _ := hA 2 (by decide)
  have a7 : f2 .xmm7 = _ := hA 3 (by decide)
  rw [a4, a5, a6, a7] at r0 r1 r2 r3
  obtain e : f3 (rw gI) = tr (acc (rowAt m1 K j 0) (vAt m1 W) 15) (acc (rowAt m1 K j 1) (vAt m1 W) 15)
      (acc (rowAt m1 K j 2) (vAt m1 W) 15) (acc (rowAt m1 K j 3) (vAt m1 W) 15) gI := by
    rcases cases4 hgI with rfl | rfl | rfl | rfl
    exacts [r0, r1, r2, r3]
  rw [h4 gI hgI, e]
  refine word_ext fun p hp => ?_
  rw [byte_of_dword _ _ hp]
  refine (byte_entries (a := fun p => acc (rowAt m1 K j p) (vAt m1 W) 15) cst_T hgI hc hp).trans ?_
  rw [sq, ← hS]
  exact acc_entry hj hp (by omega) hV ((byte_hi (by omega) (cst_M _ (by omega))).trans (by rw [hIO _ (by omega)]))
    ((byte_lo (cst_M _ (by omega))).trans (by rw [hIO _ (by omega)]))

/-- F with S-box `j`'s entries `e`, from F so far `o`. -/
def cmb (j : Nat) (e o : BitVec 128) : BitVec 128 :=
  if j = 0 then e else if j = 2 then XBinOp.eval .pxor e o else XBinOp.eval .paddd e o

/-- F so far and an S-box's entries, by `op`, to F, for the blocks `4g` to `4g + 3`. -/
theorem acc_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {op : XBinOp} {g : Nat} (hg : g < 4)
    (k : ∀ f', (∀ q, q ≠ rw g → q ≠ .xmm6 → f' q = f q) →
      WP isa (.block is) (S s (m.writeW (slot W (fOff g)) (op.eval (f (rw g)) (m.readW (slot W (fOff g)) 128))) f') Q) :
    WP isa (.block (ld .xmm6 .edi (fOff g) :: x op (rw g) .xmm6 :: stx .edi (fOff g) (rw g) :: is)) (S s m f) Q := by
  have h6 := rw_ne6 g hg
  refine wp_ldW E (by simp only [fOff]; omega) (by simp only [fOff]; omega) (wp_bin (wp_stW E
    (by simp only [fOff]; omega) (by simp only [fOff]; omega) ?_))
  simp only [upd_self, upd_ne _ _ h6]
  exact k _ fun q a b => by rw [upd_ne _ _ a, upd_ne _ _ b]

/-- S-box `j < 3` into F, for the blocks `4g` to `4g + 3`. -/
theorem combine_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {j g : Nat} (hj : j < 3) (hg : g < 4)
    (k : ∀ f', (∀ q, q ≠ rw g → q ≠ .xmm6 → f' q = f q) →
      WP isa (.block is) (S s (m.writeW (slot W (fOff g)) (cmb j (f (rw g)) (m.readW (slot W (fOff g)) 128))) f') Q) :
    WP isa (.block (combine j g ++ is)) (S s m f) Q := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · show WP isa (.block (stx .edi (fOff g) (rw g) :: is)) _ _
    exact wp_stW E (by simp only [fOff]; omega) (by simp only [fOff]; omega) (k f fun _ _ _ => rfl)
  · show WP isa (.block (ld .xmm6 .edi (fOff g) :: x .paddd (rw g) .xmm6 :: stx .edi (fOff g) (rw g) :: is)) _ _
    exact acc_wp E hg k
  · show WP isa (.block (ld .xmm6 .edi (fOff g) :: x .pxor (rw g) .xmm6 :: stx .edi (fOff g) (rw g) :: is)) _ _
    exact acc_wp E hg k

/-- S-box 3 into F, and F exclusive-ored with xR, to xL, for the blocks `4g` to `4g + 3`. -/
theorem last_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {g : Nat} (hg : g < 4)
    (k : ∀ f', (∀ q, q ≠ rw g → q ≠ .xmm6 → f' q = f q) →
      WP isa (.block is) (S s (m.writeW (slot W (xlOff g)) (XBinOp.eval .pxor (XBinOp.eval .paddd (f (rw g))
        (m.readW (slot W (fOff g)) 128)) (m.readW (slot W (xrOff g)) 128))) f') Q) :
    WP isa (.block (combine 3 g ++ is)) (S s m f) Q := by
  have h6 := rw_ne6 g hg
  show WP isa (.block (ld .xmm6 .edi (fOff g) :: x .paddd (rw g) .xmm6 :: ld .xmm6 .edi (xrOff g) ::
    x .pxor (rw g) .xmm6 :: stx .edi (xlOff g) (rw g) :: is)) _ _
  refine wp_ldW E (by simp only [fOff]; omega) (by simp only [fOff]; omega) (wp_bin (wp_ldW E
    (by simp only [xrOff]; omega) (by simp only [xrOff]; omega) (wp_bin (wp_stW E (by simp only [xlOff]; omega)
    (by simp only [xlOff]; omega) ?_))))
  simp only [upd_self, upd_ne _ _ h6]
  exact k _ fun q a b => by rw [upd_ne _ _ a, upd_ne _ _ b, upd_ne _ _ a, upd_ne _ _ b]

theorem sbox_eq (j : Nat) (is : List Instr) :
    Impl.Blowfish.X86.Ssse3.Wide.sbox j ++ is = Impl.Blowfish.X86.Ssse3.Wide.nibbles j ++
      ((List.range' 0 16).flatMap index ++ (scan j ++ (entries ++ ((List.range' 0 4).flatMap (combine j) ++ is)))) := by
  rw [Impl.Blowfish.X86.Ssse3.Wide.sbox, List.range_eq_range', List.range_eq_range']
  simp only [List.append_assoc]

theorem vR_sub (W : BitVec 32) : Region.Sub (vR W) (wR16 W) := Region.sub_prefix (by decide)

/-- S-box `j < 3` into F, for the groups `g` to `g + n - 1`: the entries
`e`, in their registers, and F so far `o`. -/
theorem combines_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop} {j : Nat}
    (hj : j < 3) {e o : Nat → BitVec 128} {m₁ : Mem} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128),
      g + n ≤ 4 → (∀ g' < 4, g ≤ g' → f (rw g') = e g') →
      (∀ g' < 4, g ≤ g' → m.readW (slot W (fOff g')) 128 = o g') →
      (∀ g' < g, m.readW (slot W (fOff g')) 128 = cmb j (e g') (o g')) → Same W 384 768 m₁ m →
      Frame [wR16 W] m₁ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (fOff g')) 128 = cmb j (e g') (o g')) → Same W 384 768 m₁ m' →
        Frame [wR16 W] m₁ m' → WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap (combine j) ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ hw hs hf k => k m f hw hs hf
  | succ n ih =>
    intro g m f hn he ho hw hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine combine_wp E hj (by omega) fun f' keep => ?_
    rw [he g (by omega) (Nat.le_refl _), ho g (by omega) (Nat.le_refl _)]
    refine ih (g + 1) _ f' (by omega) (fun g' h4 hg' => ?_) (fun g' h4 hg' => ?_) (fun g' hg' => ?_)
      (hs.write _ (.inl (by simp only [fOff]; omega)) (by decide) (by simp only [fOff]; omega))
      (hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [fOff]; omega) (by simp only [fOff]; omega)))
      fun m' f'' hw' hs' hf' => k m' f'' (fun g' hg' => hw' g' (by omega)) hs' hf'
    · rw [keep _ (rw_ne g' h4 g (by omega) (by omega)) (rw_ne6 g' h4)]; exact he g' h4 (by omega)
    · exact (rd_wr m W _ (by simp only [fOff]; omega) (by simp only [fOff]; omega)
        (by simp only [fOff]; omega)).trans (ho g' h4 (by omega))
    · by_cases e' : g' = g
      · rw [e']; exact readW_self128 _ _ _
      · exact (rd_wr m W _ (by simp only [fOff]; omega) (by simp only [fOff]; omega)
          (by simp only [fOff]; omega)).trans (hw g' (by omega))

/-- S-box 3 into F and the new xL, for the groups `g` to `g + n - 1`: the
entries `e`, F so far `o` and xR `r`. -/
theorem lasts_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop}
    {e o r : Nat → BitVec 128} {m₁ : Mem} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128),
      g + n ≤ 4 → (∀ g' < 4, g ≤ g' → f (rw g') = e g') →
      (∀ g' < 4, m.readW (slot W (fOff g')) 128 = o g') → (∀ g' < 4, m.readW (slot W (xrOff g')) 128 = r g') →
      (∀ g' < g, m.readW (slot W (xlOff g')) 128 =
        XBinOp.eval .pxor (XBinOp.eval .paddd (e g') (o g')) (r g')) → Same W 576 768 m₁ m →
      Same W 384 512 m₁ m → Frame [wR16 W] m₁ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (xlOff g')) 128 =
          XBinOp.eval .pxor (XBinOp.eval .paddd (e g') (o g')) (r g')) → Same W 576 768 m₁ m' →
        Same W 384 512 m₁ m' → Frame [wR16 W] m₁ m' → WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap (combine 3) ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ _ hw hs hb hf k => k m f hw hs hb hf
  | succ n ih =>
    intro g m f hn he ho hr hw hs hb hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine last_wp E (by omega) fun f' keep => ?_
    rw [he g (by omega) (Nat.le_refl _), ho g (by omega), hr g (by omega)]
    refine ih (g + 1) _ f' (by omega) (fun g' h4 hg' => ?_) (fun g' h4 => ?_) (fun g' h4 => ?_) (fun g' hg' => ?_)
      (hs.write _ (.inl (by simp only [xlOff]; omega)) (by decide) (by simp only [xlOff]; omega))
      (hb.write _ (.inr (by simp only [xlOff]; omega)) (by decide) (by simp only [xlOff]; omega))
      (hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [xlOff]; omega) (by simp only [xlOff]; omega)))
      fun m' f'' hw' hs' hb' hf' => k m' f'' (fun g' hg' => hw' g' (by omega)) hs' hb' hf'
    · rw [keep _ (rw_ne g' h4 g (by omega) (by omega)) (rw_ne6 g' h4)]; exact he g' h4 (by omega)
    · exact (rd_wr m W _ (by simp only [fOff, xlOff]; omega) (by simp only [fOff]; omega)
        (by simp only [xlOff]; omega)).trans (ho g' h4)
    · exact (rd_wr m W _ (by simp only [xrOff, xlOff]; omega) (by simp only [xrOff]; omega)
        (by simp only [xlOff]; omega)).trans (hr g' h4)
    · by_cases e' : g' = g
      · rw [e']; exact readW_self128 _ _ _
      · exact (rd_wr m W _ (by simp only [xlOff]; omega) (by simp only [xlOff]; omega)
          (by simp only [xlOff]; omega)).trans (hw g' (by omega))

/-- xL after the entry of P (`tvv`, at its places) to xR, for the groups `g` to `g + n - 1`. -/
theorem toRs_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop}
    {tvv : Nat → BitVec 128} {m₁ : Mem} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 →
      (∀ g' < 4, m.readW (slot W (tOff g')) 128 = tvv g') → (∀ g' < g, m.readW (slot W (xrOff g')) 128 = tvv g') →
      Same W 384 576 m₁ m → Frame [wR16 W] m₁ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (xrOff g')) 128 = tvv g') → Same W 384 576 m₁ m' →
        Frame [wR16 W] m₁ m' → WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap toR ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ hw hs hf k => k m f hw hs hf
  | succ n ih =>
    intro g m f hn ht hw hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    show WP isa (.block (ld .xmm0 .edi (tOff g) :: stx .edi (xrOff g) .xmm0 :: _)) _ _
    refine wp_ldW E (by simp only [tOff]; omega) (by simp only [tOff]; omega) (wp_stW E
      (by simp only [xrOff]; omega) (by simp only [xrOff]; omega) ?_)
    rw [upd_self, ht g (by omega)]
    refine ih (g + 1) _ _ (by omega) (fun g' h4 => ?_) (fun g' hg' => ?_)
      (hs.write _ (.inr (by simp only [xrOff]; omega)) (by decide) (by simp only [xrOff]; omega))
      (hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [xrOff]; omega) (by simp only [xrOff]; omega)))
      fun m' f'' hw' hs' hf' => k m' f'' (fun g' hg' => hw' g' (by omega)) hs' hf'
    · exact (rd_wr m W _ (by simp only [tOff, xrOff]; omega) (by simp only [tOff]; omega)
        (by simp only [xrOff]; omega)).trans (ht g' h4)
    · by_cases e' : g' = g
      · rw [e']; exact readW_self128 _ _ _
      · exact (rd_wr m W _ (by simp only [xrOff]; omega) (by simp only [xrOff]; omega)
          (by simp only [xrOff]; omega)).trans (hw g' (by omega))

/-- **S-box `j < 3` of the sixteen blocks, into F**: F of the first `j + 1`
S-boxes for every block; the places from the buffer on are kept. -/
theorem sboxF_wp {K W P : BitVec 32} (E : Env16 K W P s) (dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR16 W))
    {t : Nat → BitVec 32} {SK : Schedule} {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {j : Nat}
    (hj : j < 3) (hSK : scheduleAt m (K.setWidth 64) = SK)
    (hIO : ∀ i < 16, byte (m.readW (slot W (ioOff (3 - j))) 128) i = quarter (t i) j)
    (hF : 0 < j → ∀ g < 4, ∀ k < 4, dword (m.readW (slot W (fOff g)) 128) k = fAcc SK (t (4 * g + k)) (j - 1))
    (k : ∀ m' g', Same W 384 768 m m' → Frame [wR16 W] m m' →
      (∀ g < 4, ∀ k < 4, dword (m'.readW (slot W (fOff g)) 128) k = fAcc SK (t (4 * g + k)) j) →
      WP isa (.block is) (S s m' g') Q) :
    WP isa (.block (Impl.Blowfish.X86.Ssse3.Wide.sbox j ++ is)) (S s m f) Q := by
  rw [sbox_eq]
  refine front_wp E (dKW.sub_right (vR_sub W)) (by omega) hIO fun m1 g1 hf1 hE => ?_
  obtain s1 : Same W 320 768 m m1 := Same.of_frame hf1 (.inl (by decide)) (by decide) (by decide)
  refine combines_wp E hj (e := fun g => g1 (rw g)) (o := fun g => m.readW (slot W (fOff g)) 128) (m₁ := m1) 4 0
    m1 g1 (by decide) (fun _ _ _ => rfl)
    (fun g' h4 _ => s1 _ (by simp only [fOff]; omega) (by simp only [fOff]; omega))
    (fun g' h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Frame.refl _ _) fun m2 g2 hw hs2 hf2 => ?_
  refine k m2 g2 ((s1.mono (by decide) (Nat.le_refl _)).trans hs2)
    ((hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact vR_sub W⟩).trans hf2) fun g hg c hc => ?_
  rw [hw g hg]
  rw [hSK] at hE
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hE g hg c hc
  · show dword (XBinOp.eval .paddd (g1 (rw g)) (m.readW (slot W (fOff g)) 128)) c = _
    rw [dword_paddd _ _ hc, hE g hg c hc, hF (by decide) g hg c hc, BitVec.add_comm]; rfl
  · show dword (XBinOp.eval .pxor (g1 (rw g)) (m.readW (slot W (fOff g)) 128)) c = _
    rw [dword_pxor, hE g hg c hc, hF (by decide) g hg c hc, BitVec.xor_comm]; rfl

/-- **S-box 3 of the sixteen blocks, and the new xL**: F exclusive-ored
with xR, at xL's places; xR's places and those after them, and the buffer,
are kept. -/
theorem sboxL_wp {K W P : BitVec 32} (E : Env16 K W P s) (dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR16 W))
    {t : Nat → BitVec 32} {SK : Schedule} {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (hSK : scheduleAt m (K.setWidth 64) = SK)
    (hIO : ∀ i < 16, byte (m.readW (slot W (ioOff (3 - 3))) 128) i = quarter (t i) 3)
    (hF : ∀ g < 4, ∀ k < 4, dword (m.readW (slot W (fOff g)) 128) k = fAcc SK (t (4 * g + k)) 2)
    (k : ∀ m' g', Same W 576 768 m m' → Same W 384 512 m m' → Frame [wR16 W] m m' →
      (∀ g < 4, ∀ k < 4, dword (m'.readW (slot W (xlOff g)) 128) k =
        Spec.Blowfish.f SK (t (4 * g + k)) ^^^ dword (m.readW (slot W (xrOff g)) 128) k) →
      WP isa (.block is) (S s m' g') Q) :
    WP isa (.block (Impl.Blowfish.X86.Ssse3.Wide.sbox 3 ++ is)) (S s m f) Q := by
  rw [sbox_eq]
  refine front_wp E (dKW.sub_right (vR_sub W)) (by decide) hIO fun m1 g1 hf1 hE => ?_
  obtain s1 : Same W 320 768 m m1 := Same.of_frame hf1 (.inl (by decide)) (by decide) (by decide)
  refine lasts_wp E (e := fun g => g1 (rw g)) (o := fun g => m.readW (slot W (fOff g)) 128)
    (r := fun g => m.readW (slot W (xrOff g)) 128) (m₁ := m1) 4 0 m1 g1 (by decide) (fun _ _ _ => rfl)
    (fun g' h4 => s1 _ (by simp only [fOff]; omega) (by simp only [fOff]; omega))
    (fun g' h4 => s1 _ (by simp only [xrOff]; omega) (by simp only [xrOff]; omega))
    (fun g' h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Same.refl _ _ _ _) (Frame.refl _ _)
    fun m2 g2 hw hs2 hb2 hf2 => ?_
  refine k m2 g2 ((s1.mono (by decide) (Nat.le_refl _)).trans hs2) ((s1.mono (by decide) (by decide)).trans hb2)
    ((hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact vR_sub W⟩).trans hf2) fun g hg c hc => ?_
  rw [hw g hg]
  rw [hSK] at hE
  show dword (XBinOp.eval .pxor (XBinOp.eval .paddd (g1 (rw g)) (m.readW (slot W (fOff g)) 128))
    (m.readW (slot W (xrOff g)) 128)) c = _
  rw [dword_pxor, dword_paddd _ _ hc, hE g hg c hc, hF g hg c hc, BitVec.add_comm, ← fAcc_three]; rfl

/-! ## A round -/

/-- The halves of block `b`, in the working space. -/
def hv (m : Mem) (W : BitVec 32) (b : Nat) : BitVec 32 × BitVec 32 :=
  (dword (m.readW (slot W (xlOff (b / 4))) 128) (b % 4), dword (m.readW (slot W (xrOff (b / 4))) 128) (b % 4))

theorem dword_bc (p : BitVec 32) {k : Nat} (hk : k < 4) : dword (bc p) k = p := by
  rw [bc, Lanes.bcast_L, Lanes.dword_L _ hk]

/-- **A round of the sixteen blocks**, after its load of the entry of P (in
`eax`): `xL ^= P`, `xR ^= F(xL)` and the exchange, for every block; the
buffer is kept. -/
theorem roundV_wp {K W P : BitVec 32} (E : Env16 K W P s) (dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR16 W))
    {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {SK : Schedule}
    (hSK : scheduleAt m (K.setWidth 64) = SK)
    (k : ∀ m' g, (∀ b < 16, hv m' W b = (Spec.Blowfish.f SK ((hv m W b).1 ^^^ s.gpr .eax) ^^^ (hv m W b).2,
        (hv m W b).1 ^^^ s.gpr .eax)) → Same W 384 512 m m' → Frame [wR16 W] m m' →
      WP isa (.block is) (S s m' g) Q) :
    WP isa (.block (planesX ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 0 ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 1 ++
      (Impl.Blowfish.X86.Ssse3.Wide.sbox 2 ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 3 ++
      ((List.range' 0 4).flatMap toR ++ is))))))) (S s m f) Q := by
  refine planesX_wp E fun m1 g1 hT hIO hs1 hf1 => ?_
  obtain dK : ∀ r ∈ [wR16 W], Region.Disjoint ⟨K.setWidth 64, 4168⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact dKW
  obtain hSK1 : scheduleAt m1 (K.setWidth 64) = SK := (scheduleAt_eq_of_frame _ hf1 dK).trans hSK
  -- xL after the entry of P, a block at a time
  obtain tT : ∀ g < 4, ∀ k < 4, dword (tv m W (bc (s.gpr .eax)) g) k = (hv m W (4 * g + k)).1 ^^^ s.gpr .eax :=
    fun g hg k hk => by
      show dword (XBinOp.eval .pxor (m.readW (slot W (xlOff g)) 128) (bc (s.gpr .eax))) k =
        dword (m.readW (slot W (xlOff ((4 * g + k) / 4))) 128) ((4 * g + k) % 4) ^^^ s.gpr .eax
      rw [dword_pxor, dword_bc _ hk, show (4 * g + k) / 4 = g by omega, show (4 * g + k) % 4 = k by omega]
  obtain ⟨t, ht⟩ : ∃ t : Nat → BitVec 32, t = fun b => (hv m W b).1 ^^^ s.gpr .eax := ⟨_, rfl⟩
  obtain io1 : ∀ b' < 4, ∀ i < 16, byte (m1.readW (slot W (ioOff b')) 128) i = (t i).extractLsb' (8 * b') 8 :=
    fun b' hb' i hi => by
      rw [hIO b' hb']
      have h := byte_planes (X := fun g => tv m W (bc (s.gpr .eax)) g) cst_T (g := i / 4) (k := i % 4) (b := b')
        (by omega) (by omega) hb'
      rw [show 4 * (i / 4) + i % 4 = i by omega] at h
      refine h.trans ?_
      show (dword (tv m W (bc (s.gpr .eax)) (i / 4)) (i % 4)).extractLsb' (8 * b') 8 = _
      rw [tT (i / 4) (by omega) (i % 4) (by omega), show 4 * (i / 4) + i % 4 = i by omega, ht]
  refine sboxF_wp E dKW (t := t) (j := 0) (by decide) hSK1 (fun i hi => io1 3 (by decide) i hi)
    (fun h => absurd h (by decide)) fun m2 g2 s2 f2 F2 => ?_
  obtain hSK2 : scheduleAt m2 (K.setWidth 64) = SK := (scheduleAt_eq_of_frame _ f2 dK).trans hSK1
  refine sboxF_wp E dKW (t := t) (j := 1) (by decide) hSK2
    (fun i hi => (congrArg (byte · i) (s2 _ (by decide) (by decide))).trans (io1 2 (by decide) i hi))
    (fun _ => F2) fun m3 g3 s3 f3 F3 => ?_
  obtain hSK3 : scheduleAt m3 (K.setWidth 64) = SK := (scheduleAt_eq_of_frame _ f3 dK).trans hSK2
  obtain s13 := s2.trans s3
  refine sboxF_wp E dKW (t := t) (j := 2) (by decide) hSK3
    (fun i hi => (congrArg (byte · i) (s13 _ (by decide) (by decide))).trans (io1 1 (by decide) i hi))
    (fun _ => F3) fun m4 g4 s4 f4 F4 => ?_
  obtain hSK4 : scheduleAt m4 (K.setWidth 64) = SK := (scheduleAt_eq_of_frame _ f4 dK).trans hSK3
  obtain s14 := s13.trans s4
  refine sboxL_wp E dKW (t := t) hSK4
    (fun i hi => (congrArg (byte · i) (s14 _ (by decide) (by decide))).trans (io1 0 (by decide) i hi)) F4
    fun m5 g5 s5 b5 f5 X5 => ?_
  refine toRs_wp E (tvv := fun g => tv m W (bc (s.gpr .eax)) g) (m₁ := m5) 4 0 m5 g5 (by decide)
    (fun g' h4 => (s5 _ (by simp only [tOff]; omega) (by simp only [tOff]; omega)).trans
      ((s14 _ (by simp only [tOff]; omega) (by simp only [tOff]; omega)).trans (hT g' h4)))
    (fun g' h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Frame.refl _ _) fun m6 g6 hw hs6 hf6 => ?_
  refine k m6 g6 (fun b hb => ?_)
    ((hs1.mono (by decide) (by decide)).trans (((s14.mono (Nat.le_refl _) (by decide)).trans b5).trans
      (hs6.mono (Nat.le_refl _) (by decide))))
    ((((hf1.trans f2).trans f3).trans f4).trans (f5.trans hf6))
  -- xR of the blocks, kept until S-box 3
  obtain xr4 : ∀ g < 4, m4.readW (slot W (xrOff g)) 128 = m.readW (slot W (xrOff g)) 128 := fun g hg =>
    (s14 _ (by simp only [xrOff]; omega) (by simp only [xrOff]; omega)).trans
      (hs1 _ (by simp only [xrOff]; omega) (by simp only [xrOff]; omega))
  refine Prod.ext ?_ ?_
  · show dword (m6.readW (slot W (xlOff (b / 4))) 128) (b % 4) = _
    rw [hs6 _ (by simp only [xlOff]; omega) (by simp only [xlOff]; omega), X5 (b / 4) (by omega) (b % 4) (by omega),
      xr4 (b / 4) (by omega), show 4 * (b / 4) + b % 4 = b by omega, ht]
    rfl
  · show dword (m6.readW (slot W (xrOff (b / 4))) 128) (b % 4) = _
    rw [hw (b / 4) (by omega), tT (b / 4) (by omega) (b % 4) (by omega), show 4 * (b / 4) + b % 4 = b by omega]

open VG.Proof.Blowfish (roundStep iter iter_succ feistel_eq)
open VG.X86.Wp

theorem round_eq : Impl.Blowfish.X86.Ssse3.Wide.round = .mov .eax (.mem (at_ .edx 0)) ::
    (planesX ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 0 ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 1 ++
      (Impl.Blowfish.X86.Ssse3.Wide.sbox 2 ++ (Impl.Blowfish.X86.Ssse3.Wide.sbox 3 ++
      ((List.range' 0 4).flatMap toR ++ ([.alu .add .edx (imm 4), .alu .cmp .edx (.reg .ebp)] : List Instr))))))) := by
  rw [Impl.Blowfish.X86.Ssse3.Wide.round, planes_eq, List.range_eq_range']
  simp only [List.append_assoc, List.cons_append]

/-- What does not change while the sixteen-block function runs: the
schedule at `K`, the working space at `W` and the entries of P at `P`, in
the order `order`, apart from the bytes the function writes. -/
structure Fix16 (K W P : BitVec 32) (SK : Schedule) (order : Nat → Nat) (s₀ : State) : Prop where
  fK : K.toNat + 4168 ≤ 2 ^ 32
  fW : W.toNat + 768 ≤ 2 ^ 32
  fP : P.toNat + 72 ≤ 2 ^ 32
  rdK : ∀ o n, o + n ≤ 4168 → InRegions (s₀.rd ++ s₀.wr) (slot K o) n
  wrW : ∀ o n, 64 ≤ o → o + n ≤ 768 → InRegions s₀.wr (slot W o) n
  rdP : ∀ o n, o + n ≤ 72 → InRegions (s₀.rd ++ s₀.wr) (slot P o) n
  dKW : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (wR16 W)
  dPW : Region.Disjoint ⟨P.setWidth 64, 72⟩ (wR16 W)
  sk : scheduleAt s₀.mem (K.setWidth 64) = SK
  pv : ∀ i < 18, s₀.mem.readW (slot P (4 * i)) 32 = pEntry SK (order i)

/-- Before round `i` of the sixteen blocks: the halves in the working space,
the pointer to the round's entry of P in `edx` and its end in `ebp`. -/
structure RInv16 (s₀ : State) (K W P : BitVec 32) (SK : Schedule) (order : Nat → Nat)
    (st : Nat → BitVec 32 × BitVec 32) (i : Nat) (u : State) : Prop where
  edx : u.gpr .edx = P + BitVec.ofNat 32 (4 * i)
  ebp : u.gpr .ebp = P + BitVec.ofNat 32 64
  esi : u.gpr .esi = K
  edi : u.gpr .edi = W
  ebx : u.gpr tbr = s₀.syms tableName
  esp : u.gpr .esp = s₀.gpr .esp
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  syms : u.syms = s₀.syms
  frame : Frame [wR16 W] s₀.mem u.mem
  buf : Same W 384 512 s₀.mem u.mem
  halves : ∀ b < 16, hv u.mem W b = iter SK order i (st b)

/-- An entry of P, through what the function has written. -/
theorem Fix16.pAt {K W P : BitVec 32} {SK : Schedule} {order : Nat → Nat} {s₀ : State} (F : Fix16 K W P SK order s₀)
    {m : Mem} (hf : Frame [wR16 W] s₀.mem m) {i : Nat} (hi : i < 18) :
    m.readW (slot P (4 * i)) 32 = pEntry SK (order i) :=
  (hf.readW (r := ⟨slot P (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact F.dPW.sub_left (Offset.sub_base _ (by omega))) (by decide)).trans (F.pv i hi)

theorem Fix16.sched {K W P : BitVec 32} {SK : Schedule} {order : Nat → Nat} {s₀ : State} (F : Fix16 K W P SK order s₀)
    {m : Mem} (hf : Frame [wR16 W] s₀.mem m) : scheduleAt m (K.setWidth 64) = SK :=
  (scheduleAt_eq_of_frame _ hf fun r hr => by rw [List.mem_singleton.mp hr]; exact F.dKW).trans F.sk

/-- **A round of the sixteen blocks.** -/
theorem round_wp {s₀ : State} {K W P : BitVec 32} {SK : Schedule} {order : Nat → Nat}
    (F : Fix16 K W P SK order s₀) {i : Nat} (hi : i < 16) {st : Nat → BitVec 32 × BitVec 32} {u : State}
    (hI : RInv16 s₀ K W P SK order st i u) :
    WP isa (.block Impl.Blowfish.X86.Ssse3.Wide.round) u fun u' =>
      RInv16 s₀ K W P SK order st (i + 1) u' ∧ eval .ne u' = some (decide (i + 1 < 16)) := by
  have fP := F.fP
  obtain aP : addr (P + BitVec.ofNat 32 (4 * i)) 0 = slot P (4 * i) := by
    show (P + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by omega)
  rw [round_eq]
  refine wp_ldm hI.edx (by rw [aP, hI.rd, hI.wr]; exact F.rdP _ _ (by omega)) fun u₁ h₁ => ?_
  obtain eax₁ : u₁.gpr .eax = pEntry SK (order i) := by rw [h₁.gpr, aP]; exact F.pAt hI.frame (by omega)
  obtain E₁ : Env16 K W P u₁ := ⟨(h₁.other _ (by decide)).trans hI.esi, (h₁.other _ (by decide)).trans hI.edi,
    ((h₁.other _ (by decide)).trans hI.ebx).trans (by rw [h₁.syms, hI.syms]), F.fK, F.fW, F.fP,
    by rw [h₁.rd, h₁.wr, hI.rd, hI.wr]; exact F.rdK, by rw [h₁.wr, hI.wr]; exact F.wrW,
    by rw [h₁.rd, h₁.wr, hI.rd, hI.wr]; exact F.rdP⟩
  obtain f₁ : Frame [wR16 W] s₀.mem u₁.mem := by rw [h₁.mem]; exact hI.frame
  show WP isa _ (S u₁ u₁.mem u₁.xmm) _
  refine roundV_wp E₁ F.dKW (F.sched f₁) fun m' g hh hb hf => ?_
  refine wp_addi fun t₁ k₁ => wp_cmp fun t₂ k₂ _ z₂ => WP.block_nil ?_
  obtain edx₁ : t₁.gpr .edx = P + BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [k₁.gpr]
    show u₁.gpr .edx + BitVec.ofNat 32 4 = _
    rw [h₁.other _ (by decide), hI.edx, Offset.add_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  obtain G : ∀ r, r ≠ .edx → t₂.gpr r = u₁.gpr r := fun r a => by rw [k₂.gpr, k₁.other r a]
  refine ⟨⟨by rw [k₂.gpr]; exact edx₁, by rw [G _ (by decide), h₁.other _ (by decide)]; exact hI.ebp,
    (G _ (by decide)).trans E₁.esi, (G _ (by decide)).trans E₁.edi,
    by rw [G _ (by decide), h₁.other _ (by decide)]; exact hI.ebx,
    by rw [G _ (by decide), h₁.other _ (by decide)]; exact hI.esp,
    by rw [k₂.rd, k₁.rd]; exact h₁.rd.trans hI.rd, by rw [k₂.wr, k₁.wr]; exact h₁.wr.trans hI.wr,
    by rw [k₂.syms, k₁.syms]; exact h₁.syms.trans hI.syms, by rw [k₂.mem, k₁.mem]; exact f₁.trans hf,
    by rw [k₂.mem, k₁.mem]; exact (by rw [h₁.mem]; exact hI.buf : Same W 384 512 s₀.mem u₁.mem).trans hb,
    fun b hb' => ?_⟩, ?_⟩
  · rw [k₂.mem, k₁.mem]
    show hv m' W b = _
    rw [hh b hb', iter_succ, ← hI.halves b hb', h₁.mem, eax₁]
    rfl
  · show (t₂.zf).map (!·) = _
    rw [z₂, edx₁, k₁.other _ (by decide)]
    show some (!(P + BitVec.ofNat 32 (4 * (i + 1)) - u₁.gpr .ebp == 0)) = _
    rw [h₁.other _ (by decide), hI.ebp, Offset.add_sub_add_left, sub_beq (by omega) (by decide)]
    by_cases h : i + 1 < 16
    · simp only [h, decide_true, show ¬ 4 * (i + 1) = 64 by omega, decide_false, Bool.not_false]
    · simp only [h, decide_false, show 4 * (i + 1) = 64 by omega, decide_true, Bool.not_true]

/-! ## The blocks in -/

open VG.Spec.Blowfish (blockAt decodeWord encodeBlock)
open VG.Proof.Blowfish (decodeWord_byte blockAt_getD encodeBlock_getD blockAt_eq)

theorem cst_KL : ∀ c < 2, ∀ i < 4, byte (cst oKL) (4 * c + i) = BitVec.ofNat 8 (8 * c + 0 + 3 - i) := by lit_decide

theorem cst_KR : ∀ c < 2, ∀ i < 4, byte (cst oKR) (4 * c + i) = BitVec.ofNat 8 (8 * c + 4 + 3 - i) := by lit_decide

theorem cst_BS : ∀ d < 4, ∀ i < 4, byte (cst oBS) (4 * d + i) = BitVec.ofNat 8 (4 * d + 3 - i) := by lit_decide

theorem idx16 : ∀ n < 16, (BitVec.ofNat 8 n).msb = false ∧ ((BitVec.ofNat 8 n).extractLsb' 0 4).toNat = n := by
  decide

/-- A half of one of the two blocks of sixteen bytes, as a big-endian
doubleword, by the shuffle `Kc` whose bytes `4c + i` are `8c + o + 3 - i`. -/
theorem in_half {m : Mem} {a : Addr} {Kc : BitVec 128} {o : Nat} (ho : o ≤ 4)
    (hK : ∀ c < 2, ∀ i < 4, byte Kc (4 * c + i) = BitVec.ofNat 8 (8 * c + o + 3 - i)) {c : Nat} (hc : c < 2) :
    dword (XBinOp.eval .pshufb (m.readW a 128) Kc) c = decodeWord (blockAt m (a + BitVec.ofNat 64 (8 * c))) o := by
  refine word_ext fun i hi => ?_
  obtain ⟨e1, e2⟩ := idx16 (8 * c + o + 3 - i) (by omega)
  rw [byte_of_dword _ _ hi, ByteMap.byte_pshufb _ _ (by omega), hK c hc i hi, e1, e2, ite_eq_right Bool.false_ne_true,
    decodeWord_byte _ _ hi, blockAt_getD _ _ (by omega), Offset.add_add]
  show (m.readW a 128).extractLsb' (8 * (8 * c + o + 3 - i)) 8 = _
  rw [byte_readW _ _ (by omega), show 8 * c + (o + (3 - i)) = 8 * c + o + 3 - i by omega]

/-- A half of block `4g + k` of the buffer, in doubleword `k` of the group's register. -/
theorem in_lanes {m₀ : Mem} {W : BitVec 32} {Kc : BitVec 128} {o : Nat} (ho : o ≤ 4)
    (hK : ∀ c < 2, ∀ i < 4, byte Kc (4 * c + i) = BitVec.ofNat 8 (8 * c + o + 3 - i)) {g k : Nat} (hk : k < 4) :
    dword (XBinOp.eval .punpcklqdq (XBinOp.eval .pshufb (m₀.readW (slot W (bufOff + 32 * g)) 128) Kc)
      (XBinOp.eval .pshufb (m₀.readW (slot W (bufOff + 32 * g + 16)) 128) Kc)) k =
      decodeWord (blockAt m₀ (slot W (bufOff + 8 * (4 * g + k)))) o := by
  rw [punpcklqdq_eq]
  rcases cases4 hk with rfl | rfl | rfl | rfl
  · rw [dword_ofDwords_0, in_half ho hK (c := 0) (by decide), Offset.add_add,
      show bufOff + 32 * g + 8 * 0 = bufOff + 8 * (4 * g + 0) by omega]
  · rw [dword_ofDwords_1, in_half ho hK (c := 1) (by decide), Offset.add_add,
      show bufOff + 32 * g + 8 * 1 = bufOff + 8 * (4 * g + 1) by omega]
  · rw [dword_ofDwords_2, in_half ho hK (c := 0) (by decide), Offset.add_add,
      show bufOff + 32 * g + 16 + 8 * 0 = bufOff + 8 * (4 * g + 2) by omega]
  · rw [dword_ofDwords_3, in_half ho hK (c := 1) (by decide), Offset.add_add,
      show bufOff + 32 * g + 16 + 8 * 1 = bufOff + 8 * (4 * g + 3) by omega]

/-- The halves of the blocks `4g` to `4g + 3`, to their places. -/
theorem blockIn_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {g : Nat} (hg : g < 4)
    (k : ∀ f', f' .xmm6 = f .xmm6 → f' .xmm7 = f .xmm7 →
      WP isa (.block is) (S s ((m.writeW (slot W (xlOff g)) (XBinOp.eval .punpcklqdq
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g)) 128) (f .xmm6))
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g + 16)) 128) (f .xmm6)))).writeW (slot W (xrOff g))
        (XBinOp.eval .punpcklqdq (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g)) 128) (f .xmm7))
          (XBinOp.eval .pshufb (m.readW (slot W (bufOff + 32 * g + 16)) 128) (f .xmm7)))) f') Q) :
    WP isa (.block (blockIn g ++ is)) (S s m f) Q :=
  wp_ldW E (by simp only [bufOff]; omega) (by simp only [bufOff]; omega) (wp_ldW E (by simp only [bufOff]; omega)
    (by simp only [bufOff]; omega) (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_stW E
    (by simp only [xlOff]; omega) (by simp only [xlOff]; omega) (wp_stW E (by simp only [xrOff]; omega)
    (by simp only [xrOff]; omega) (k _ rfl rfl))))))))))))

/-- The halves of block `b` of the buffer. -/
def st0 (m₀ : Mem) (W : BitVec 32) (b : Nat) : BitVec 32 × BitVec 32 :=
  (decodeWord (blockAt m₀ (slot W (bufOff + 8 * b))) 0, decodeWord (blockAt m₀ (slot W (bufOff + 8 * b))) 4)

/-- The halves of the groups `g` to `g + n - 1`, to their places. -/
theorem blocksIn_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop} {m₀ : Mem}
    (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 → f .xmm6 = cst oKL → f .xmm7 = cst oKR →
      (∀ b < 4 * g, hv m W b = st0 m₀ W b) → Same W 384 512 m₀ m → Frame [wR16 W] m₀ m →
      (∀ m' f', (∀ b < 4 * (g + n), hv m' W b = st0 m₀ W b) → Same W 384 512 m₀ m' → Frame [wR16 W] m₀ m' →
        WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap blockIn ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ hh hs hf k => k m f hh hs hf
  | succ n ih =>
    intro g m f hn h6 h7 hh hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine blockIn_wp E (by omega) fun f' e6 e7 => ?_
    rw [h6, h7, hs _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega),
      hs _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)]
    refine ih (g + 1) _ f' (by omega) (e6.trans h6) (e7.trans h7) (fun b hb => ?_)
      ((hs.write _ (.inr (by simp only [xlOff]; omega)) (by decide) (by simp only [xlOff]; omega)).write _
        (.inr (by simp only [xrOff]; omega)) (by decide) (by simp only [xrOff]; omega))
      ((hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [xlOff]; omega)
        (by simp only [xlOff]; omega))).writeW List.mem_cons_self _ (wR16_contains W (by simp only [xrOff]; omega)
        (by simp only [xrOff]; omega)))
      fun m' f'' hh' hs' hf' => k m' f'' (fun b hb => hh' b (by omega)) hs' hf'
    by_cases hb' : b < 4 * g
    · rw [← hh b hb']
      refine Prod.ext ?_ ?_
      · show dword (Mem.readW _ (slot W (xlOff (b / 4))) 128) (b % 4) = dword (m.readW (slot W (xlOff (b / 4))) 128) (b % 4)
        rw [rd_wr _ W _ (by simp only [xlOff, xrOff]; omega) (by simp only [xlOff]; omega) (by simp only [xrOff]; omega),
          rd_wr _ W _ (by simp only [xlOff]; omega) (by simp only [xlOff]; omega) (by simp only [xlOff]; omega)]
      · show dword (Mem.readW _ (slot W (xrOff (b / 4))) 128) (b % 4) = dword (m.readW (slot W (xrOff (b / 4))) 128) (b % 4)
        rw [rd_wr _ W _ (by simp only [xrOff]; omega) (by simp only [xrOff]; omega) (by simp only [xrOff]; omega),
          rd_wr _ W _ (by simp only [xlOff, xrOff]; omega) (by simp only [xrOff]; omega) (by simp only [xlOff]; omega)]
    · obtain eg : b / 4 = g := by omega
      refine Prod.ext ?_ ?_
      · show dword (Mem.readW _ (slot W (xlOff (b / 4))) 128) (b % 4) = decodeWord _ 0
        rw [eg, rd_wr _ W _ (by simp only [xlOff, xrOff]; omega) (by simp only [xlOff]; omega)
          (by simp only [xrOff]; omega), readW_self128, in_lanes (o := 0) (by decide) cst_KL (Nat.mod_lt _ (by decide)),
          show 4 * g + b % 4 = b by omega]
      · show dword (Mem.readW _ (slot W (xrOff (b / 4))) 128) (b % 4) = decodeWord _ 4
        rw [eg, readW_self128, in_lanes (o := 4) (by decide) cst_KR (Nat.mod_lt _ (by decide)),
          show 4 * g + b % 4 = b by omega]

/-! ## The blocks out -/

/-- Two doublewords of a register stored through the shuffle that reverses
each doubleword's bytes: a block of their big-endian bytes. -/
theorem out_half {m : Mem} {a : Addr} {v : BitVec 128} (h : m.readW a 128 = XBinOp.eval .pshufb v (cst oBS)) {d : Nat}
    (hd : d + 1 < 4) : blockAt m (a + BitVec.ofNat 64 (4 * d)) = encodeBlock (dword v d) (dword v (d + 1)) := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [Offset.add_add, ← byte_readW m a (w := 128) (k := 4 * d + i) (by omega), h, encodeBlock_getD _ _ hi]
  show byte (XBinOp.eval .pshufb v (cst oBS)) (4 * d + i) = _
  by_cases h4 : i < 4
  · obtain ⟨e1, e2⟩ := idx16 (4 * d + 3 - i) (by omega)
    rw [ite_eq_left h4, ByteMap.byte_pshufb _ _ (by omega), cst_BS d (by omega) i h4, e1, e2,
      ite_eq_right Bool.false_ne_true, byte_of_dword _ _ (by omega), show 4 * d + (3 - i) = 4 * d + 3 - i by omega]
  · obtain ⟨e1, e2⟩ := idx16 (4 * (d + 1) + 3 - (i - 4)) (by omega)
    rw [ite_eq_right h4, show 4 * d + i = 4 * (d + 1) + (i - 4) by omega, ByteMap.byte_pshufb _ _ (by omega),
      cst_BS (d + 1) (by omega) (i - 4) (by omega), e1, e2, ite_eq_right Bool.false_ne_true,
      show 7 - i = 3 - (i - 4) by omega, byte_of_dword _ _ (by omega),
      show 4 * (d + 1) + (3 - (i - 4)) = 4 * (d + 1) + 3 - (i - 4) by omega]

/-- Block `4g + k` of the buffer, from doubleword `k` of the group's two registers. -/
theorem out_lanes {m : Mem} {W : BitVec 32} {A B : BitVec 128} {g : Nat}
    (h0 : m.readW (slot W (bufOff + 32 * g)) 128 = XBinOp.eval .pshufb (XBinOp.eval .punpckldq A B) (cst oBS))
    (h1 : m.readW (slot W (bufOff + 32 * g + 16)) 128 = XBinOp.eval .pshufb (XBinOp.eval .punpckhdq A B) (cst oBS))
    {k : Nat} (hk : k < 4) :
    blockAt m (slot W (bufOff + 8 * (4 * g + k))) = encodeBlock (dword A k) (dword B k) := by
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

/-- The first two blocks of a group as they are stored: xR and xL (`r`, `l`)
with the last two entries of P, a block's two doublewords together, their
bytes reversed. -/
abbrev oL (r l p7 p6 bs : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pshufb (XBinOp.eval .punpckldq (XBinOp.eval .pxor r p7) (XBinOp.eval .pxor l p6)) bs

/-- The last two blocks of a group. -/
abbrev oH (r l p7 p6 bs : BitVec 128) : BitVec 128 :=
  XBinOp.eval .pshufb (XBinOp.eval .punpckhdq (XBinOp.eval .pxor r p7) (XBinOp.eval .pxor l p6)) bs

/-- The blocks `4g` to `4g + 3`, from their halves to the buffer. -/
theorem blockOut_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {is : List Instr}
    {Q : State → Prop} {g : Nat} (hg : g < 4)
    (k : ∀ f', f' .xmm5 = f .xmm5 → f' .xmm6 = f .xmm6 → f' .xmm7 = f .xmm7 →
      WP isa (.block is) (S s ((m.writeW (slot W (bufOff + 32 * g)) (oL (m.readW (slot W (xrOff g)) 128)
          (m.readW (slot W (xlOff g)) 128) (f .xmm7) (f .xmm6) (f .xmm5))).writeW (slot W (bufOff + 32 * g + 16))
        (oH (m.readW (slot W (xrOff g)) 128) (m.readW (slot W (xlOff g)) 128) (f .xmm7) (f .xmm6) (f .xmm5))) f') Q) :
    WP isa (.block (Impl.Blowfish.X86.Ssse3.Wide.blockOut g ++ is)) (S s m f) Q :=
  wp_ldW E (by simp only [xrOff]; omega) (by simp only [xrOff]; omega) (wp_bin (wp_ldW E (by simp only [xlOff]; omega)
    (by simp only [xlOff]; omega) (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_bin (wp_stW E
    (by simp only [bufOff]; omega) (by simp only [bufOff]; omega) (wp_stW E (by simp only [bufOff]; omega)
    (by simp only [bufOff]; omega) (k _ rfl rfl rfl)))))))))))

/-- The blocks of the groups `g` to `g + n - 1`, to the buffer. -/
theorem blockOuts_wp {K W P : BitVec 32} (E : Env16 K W P s) {is : List Instr} {Q : State → Prop} {m₀ : Mem}
    {p6 p7 : BitVec 128} (n : Nat) : ∀ (g : Nat) (m : Mem) (f : XReg → BitVec 128), g + n ≤ 4 →
      f .xmm5 = cst oBS → f .xmm6 = p6 → f .xmm7 = p7 →
      (∀ g' < g, m.readW (slot W (bufOff + 32 * g')) 128 = oL (m₀.readW (slot W (xrOff g')) 128)
          (m₀.readW (slot W (xlOff g')) 128) p7 p6 (cst oBS) ∧
        m.readW (slot W (bufOff + 32 * g' + 16)) 128 = oH (m₀.readW (slot W (xrOff g')) 128)
          (m₀.readW (slot W (xlOff g')) 128) p7 p6 (cst oBS)) →
      Same W 512 640 m₀ m → Frame [wR16 W] m₀ m →
      (∀ m' f', (∀ g' < g + n, m'.readW (slot W (bufOff + 32 * g')) 128 = oL (m₀.readW (slot W (xrOff g')) 128)
          (m₀.readW (slot W (xlOff g')) 128) p7 p6 (cst oBS) ∧
        m'.readW (slot W (bufOff + 32 * g' + 16)) 128 = oH (m₀.readW (slot W (xrOff g')) 128)
          (m₀.readW (slot W (xlOff g')) 128) p7 p6 (cst oBS)) → Frame [wR16 W] m₀ m' →
        WP isa (.block is) (S s m' f') Q) →
      WP isa (.block ((List.range' g n).flatMap Impl.Blowfish.X86.Ssse3.Wide.blockOut ++ is)) (S s m f) Q := by
  induction n with
  | zero => exact fun g m f _ _ _ _ hh _ hf k => k m f hh hf
  | succ n ih =>
    intro g m f hn h5 h6 h7 hh hs hf k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    refine blockOut_wp E (by omega) fun f' e5 e6 e7 => ?_
    rw [h5, h6, h7, hs (xrOff g) (by simp only [xrOff]; omega) (by simp only [xrOff]; omega),
      hs (xlOff g) (by simp only [xlOff]; omega) (by simp only [xlOff]; omega)]
    refine ih (g + 1) _ f' (by omega) (e5.trans h5) (e6.trans h6) (e7.trans h7) (fun g' hg' => ?_)
      ((hs.write _ (.inl (by simp only [bufOff]; omega)) (by decide) (by simp only [bufOff]; omega)).write _
        (.inl (by simp only [bufOff]; omega)) (by decide) (by simp only [bufOff]; omega))
      ((hf.writeW List.mem_cons_self _ (wR16_contains W (by simp only [bufOff]; omega)
        (by simp only [bufOff]; omega))).writeW List.mem_cons_self _ (wR16_contains W (by simp only [bufOff]; omega)
        (by simp only [bufOff]; omega)))
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

/-- `blocksOut` after its loads of the last two entries of P. -/
def blocksOutX : List Instr :=
  ([.xop (.movd .xmm6 .eax), .xop (.pshufd .xmm6 .xmm6 0), .xop (.movd .xmm7 .ecx), .xop (.pshufd .xmm7 .xmm7 0),
    tb .xmm5 oBS] : List Instr) ++ ((List.range' 0 4).flatMap Impl.Blowfish.X86.Ssse3.Wide.blockOut ++ [])

theorem blocksOut_eq :
    blocksOut = .mov .eax (.mem (at_ .edx 0)) :: .mov .ecx (.mem (at_ .edx 4)) :: blocksOutX := by
  rw [blocksOut, blocksOutX, List.range_eq_range', List.append_nil]
  rfl

/-- **The sixteen blocks out**: the halves after the last round, exchanged
and with the last two entries of P (in `eax` and `ecx`), as the blocks of
the buffer. -/
theorem blocksOutX_wp {K W P : BitVec 32} (E : Env16 K W P s) {f : XReg → BitVec 128} {Q : State → Prop}
    (k : ∀ m' g, (∀ b < 16, blockAt m' (slot W (bufOff + 8 * b)) =
        encodeBlock ((hv m W b).2 ^^^ s.gpr .ecx) ((hv m W b).1 ^^^ s.gpr .eax)) → Frame [wR16 W] m m' →
      Q (S s m' g)) :
    WP isa (.block blocksOutX) (S s m f) Q := by
  rw [blocksOutX]
  simp only [List.cons_append, List.nil_append]
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_tbE E (by decide) (blockOuts_wp E (m₀ := m)
    (p6 := bc (s.gpr .eax)) (p7 := bc (s.gpr .ecx)) 4 0 m _ (by decide) rfl rfl rfl
    (fun g' h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Frame.refl _ _) fun m' f' hh hf =>
    WP.block_nil (k m' f' (fun b hb => ?_) hf))))))
  obtain ⟨h0, h1⟩ := hh (b / 4) (by omega)
  have h := out_lanes h0 h1 (k := b % 4) (Nat.mod_lt _ (by decide))
  rw [show 4 * (b / 4) + b % 4 = b by omega, dword_pxor, dword_pxor, dword_bc _ (Nat.mod_lt _ (by decide)),
    dword_bc _ (Nat.mod_lt _ (by decide))] at h
  exact h

/-! ## The function -/

theorem blocksIn_eq : blocksIn = tb .xmm6 oKL :: tb .xmm7 oKR :: ((List.range' 0 4).flatMap blockIn ++ []) := by
  rw [blocksIn, List.range_eq_range', List.append_nil]
  rfl

/-- The blocks' halves, through what is written apart from the working space. -/
theorem st0_frame {rs : List Region} {m m' : Mem} {W : BitVec 32} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (wR16 W) r) {b : Nat} (hb : b < 16) : st0 m' W b = st0 m W b := by
  rw [st0, st0, blockAt_frame hf (p := slot W (bufOff + 8 * b)) fun r hr =>
    (hd r hr).sub_left (Offset.sub _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega))]

/-- **The sixteen-block function**: the blocks at byte 384 of the working
space at `edi`, each replaced by Blowfish's Feistel network of it under the
schedule at `esi` with the entries of P at `edx`, in their order of use; it
writes the working space's bytes 64 to 767 and the four bytes below `esp`. -/
theorem cryptBlocks_wp {s : State} {K W P : BitVec 32} {SK : Schedule} {order : Nat → Nat}
    (F : Fix16 K W P SK order s) (hK : s.gpr .esi = K) (hW : s.gpr .edi = W) (hP : s.gpr .edx = P)
    (hsp : 4 ≤ (s.gpr .esp).toNat) (dKS : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (below (s.gpr .esp) 4))
    (dPS : Region.Disjoint ⟨P.setWidth 64, 72⟩ (below (s.gpr .esp) 4))
    (dWS : Region.Disjoint (wR16 W) (below (s.gpr .esp) 4)) :
    WP isa cryptBlocks s fun s' =>
      (∀ b < 16, blockAt s'.mem (slot W (bufOff + 8 * b)) =
        encodeBlock (Spec.Blowfish.feistel SK order (st0 s.mem W b).1 (st0 s.mem W b).2).1
          (Spec.Blowfish.feistel SK order (st0 s.mem W b).1 (st0 s.mem W b).2).2) ∧
      s'.gpr .esi = K ∧ s'.gpr .edi = W ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.syms = s.syms ∧ Frame [wR16 W, below (s.gpr .esp) 4] s.mem s'.mem := by
  have fP := F.fP
  refine WP.seq (WP.mono (symFrame_ok tableName s hsp) fun s₀ h₀ => WP.seq ?_)
  show WP isa (.block (.mov tbr (.reg .eax) :: .mov .ebp (.reg .edx) :: .alu .add .ebp (imm 64) :: blocksIn)) s₀ _
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => ?_
  obtain RD : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h₀.rd]
  obtain WR : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h₀.wr]
  obtain SY : s₃.syms = s.syms := by rw [u₃.syms, u₂.syms, u₁.syms, h₀.syms]
  obtain M : s₃.mem = s₀.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain G : ∀ r, r ≠ tbr → r ≠ .ebp → r ≠ .eax → r ≠ .ecx → s₃.gpr r = s.gpr r := fun r a b c d => by
    rw [u₃.other r b, u₂.other r b, u₁.other r a]
    exact h₀.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨c, d⟩)
  obtain ebx₃ : s₃.gpr tbr = s₃.syms tableName := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h₀.addr, SY]
  obtain ebp₃ : s₃.gpr .ebp = P + BitVec.ofNat 32 64 := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), h₀.gpr _ (by decide), hP]
  obtain f₀ : Frame [below (s.gpr .esp) 4] s.mem s₃.mem := by rw [M]; exact h₀.frame
  obtain F₃ : Fix16 K W P SK order s₃ := ⟨F.fK, F.fW, F.fP, by rw [RD, WR]; exact F.rdK, by rw [WR]; exact F.wrW,
    by rw [RD, WR]; exact F.rdP, F.dKW, F.dPW,
    (scheduleAt_eq_of_frame _ f₀ fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS).trans F.sk,
    fun i hi => (f₀.readW (r := ⟨slot P (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dPS.sub_left (Offset.sub_base _ (by omega))) (by decide)).trans (F.pv i hi)⟩
  obtain E₃ : Env16 K W P s₃ := ⟨(G _ (by decide) (by decide) (by decide) (by decide)).trans hK,
    (G _ (by decide) (by decide) (by decide) (by decide)).trans hW, ebx₃, F.fK, F.fW, F.fP, F₃.rdK, F₃.wrW, F₃.rdP⟩
  rw [blocksIn_eq]
  show WP isa _ (S s₃ s₃.mem s₃.xmm) _
  refine wp_tbE E₃ (by decide) (wp_tbE E₃ (by decide) (blocksIn_wp E₃ (m₀ := s₃.mem) 4 0 s₃.mem _ (by decide) rfl rfl
    (fun b h => absurd h (Nat.not_lt_zero _)) (Same.refl _ _ _ _) (Frame.refl _ _) fun m₄ f₄ hh₄ hs₄ hf₄ =>
    WP.block_nil ?_))
  -- the sixteen rounds
  refine WP.seq (WP.mono (count_loop (n := 16) (I := fun i u => RInv16 s₃ K W P SK order (st0 s₃.mem W) i u)
    (by decide) ⟨((G _ (by decide) (by decide) (by decide) (by decide)).trans hP).trans (BitVec.add_zero P).symm,
      ebp₃, E₃.esi, E₃.edi, ebx₃, rfl, rfl, rfl, rfl, hf₄, hs₄, fun b hb => hh₄ b (by omega)⟩
    fun t u ht hI => round_wp F₃ ht hI) fun s₆ h₆ => ?_)
  -- the blocks out
  obtain a16 : addr (P + BitVec.ofNat 32 (4 * 16)) 0 = slot P (4 * 16) := by
    show (P + BitVec.ofNat 32 (4 * 16) + BitVec.ofNat 32 0).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by omega)
  obtain a17 : addr (P + BitVec.ofNat 32 (4 * 16)) 4 = slot P (4 * 17) := by
    show (P + BitVec.ofNat 32 (4 * 16) + BitVec.ofNat 32 4).setWidth 64 = _
    rw [Offset.add_add]; exact addr_of_fit (by omega)
  rw [blocksOut_eq]
  refine wp_ldm h₆.edx (by rw [a16, h₆.rd, h₆.wr]; exact F₃.rdP _ _ (by decide)) fun v₁ w₁ =>
    wp_ldm ((w₁.other _ (by decide)).trans h₆.edx)
      (by rw [a17, w₁.rd, w₁.wr, h₆.rd, h₆.wr]; exact F₃.rdP _ _ (by decide)) fun v₂ w₂ => ?_
  obtain M₂ : v₂.mem = s₆.mem := by rw [w₂.mem, w₁.mem]
  obtain eax₂ : v₂.gpr .eax = pEntry SK (order 16) := by
    rw [w₂.other _ (by decide), w₁.gpr, a16]; exact F₃.pAt h₆.frame (by decide)
  obtain ecx₂ : v₂.gpr .ecx = pEntry SK (order 17) := by
    rw [w₂.gpr, w₁.mem, a17]; exact F₃.pAt h₆.frame (by decide)
  obtain G₂ : ∀ r, r ≠ .eax → r ≠ .ecx → v₂.gpr r = s₆.gpr r := fun r a b => by rw [w₂.other r b, w₁.other r a]
  obtain RD₂ : v₂.rd = s₃.rd := by rw [w₂.rd, w₁.rd, h₆.rd]
  obtain WR₂ : v₂.wr = s₃.wr := by rw [w₂.wr, w₁.wr, h₆.wr]
  obtain SY₂ : v₂.syms = s₃.syms := by rw [w₂.syms, w₁.syms, h₆.syms]
  obtain E₂ : Env16 K W P v₂ := ⟨(G₂ _ (by decide) (by decide)).trans h₆.esi,
    (G₂ _ (by decide) (by decide)).trans h₆.edi, by rw [G₂ _ (by decide) (by decide), SY₂]; exact h₆.ebx,
    F.fK, F.fW, F.fP, by rw [RD₂, WR₂]; exact F₃.rdK, by rw [WR₂]; exact F₃.wrW, by rw [RD₂, WR₂]; exact F₃.rdP⟩
  show WP isa _ (S v₂ v₂.mem v₂.xmm) _
  refine blocksOutX_wp E₂ fun m' g hb hf => ⟨fun b hb' => ?_, E₂.esi, E₂.edi,
    ((G₂ _ (by decide) (by decide)).trans h₆.esp).trans (G _ (by decide) (by decide) (by decide) (by decide)),
    RD₂.trans RD, WR₂.trans WR, SY₂.trans SY, ?_⟩
  · have h := hb b hb'
    rw [M₂, h₆.halves b hb', ecx₂, eax₂,
      st0_frame f₀ (fun r hr => by rw [List.mem_singleton.mp hr]; exact dWS) hb'] at h
    rw [feistel_eq]
    exact h
  · rw [M₂] at hf
    refine (f₀.mono fun r hr => List.mem_cons_of_mem _ hr).trans ((h₆.frame.trans hf).mono fun r hr => ?_)
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self

/-! ## The call -/

/-- **The call of the sixteen-block function**, with eight bytes of stack
apart from the schedule, from the entries of P and from the working space. -/
theorem call_wp {s : State} {K W P : BitVec 32} {SK : Schedule} {order : Nat → Nat} (F : Fix16 K W P SK order s)
    (hK : s.gpr .esi = K) (hW : s.gpr .edi = W) (hP : s.gpr .edx = P) (hsp : 8 ≤ (s.gpr .esp).toNat)
    (dKS : Region.Disjoint ⟨K.setWidth 64, 4168⟩ (below (s.gpr .esp) 8))
    (dPS : Region.Disjoint ⟨P.setWidth 64, 72⟩ (below (s.gpr .esp) 8))
    (dWS : Region.Disjoint (wR16 W) (below (s.gpr .esp) 8)) {Q : State → Prop}
    (hQ : ∀ s', (∀ b < 16, blockAt s'.mem (slot W (bufOff + 8 * b)) =
        encodeBlock (Spec.Blowfish.feistel SK order (st0 s.mem W b).1 (st0 s.mem W b).2).1
          (Spec.Blowfish.feistel SK order (st0 s.mem W b).1 (st0 s.mem W b).2).2) →
      s'.gpr .esi = K → s'.gpr .edi = W → s'.gpr .esp = s.gpr .esp → s'.rd = s.rd → s'.wr = s.wr →
      s'.syms = s.syms → Frame [wR16 W, below (s.gpr .esp) 8] s.mem s'.mem → Q s') :
    WP isa (.call fnName cryptBlocks) s Q := by
  have fP := F.fP
  obtain ⟨r4, r8, d48⟩ := call_regions hsp
  obtain cm : s.callEntry.mem = s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0) := State.callEntry_mem s
  obtain fc : Frame [below (s.gpr .esp) 8] s.mem s.callEntry.mem := by
    rw [cm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_top (by decide) hsp (by decide))
  obtain esp' : s.callEntry.gpr .esp = s.gpr .esp - 4 := State.callEntry_esp s
  refine WP.callBody (WP.mono (cryptBlocks_wp (s := s.callEntry) (SK := SK) (order := order)
    ⟨F.fK, F.fW, F.fP, F.rdK, F.wrW, F.rdP, F.dKW, F.dPW,
      (scheduleAt_eq_of_frame _ fc fun r hr => by rw [List.mem_singleton.mp hr]; exact dKS).trans F.sk,
      fun i hi => (fc.readW (r := ⟨slot P (4 * i), 4⟩) (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact dPS.sub_left (Offset.sub_base _ (by omega))) (by decide)).trans
        (F.pv i hi)⟩
    ((State.callEntry_gpr s (by decide)).trans hK) ((State.callEntry_gpr s (by decide)).trans hW)
    ((State.callEntry_gpr s (by decide)).trans hP)
    (by rw [esp', show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.X86.sub_toNat (by omega)]; omega)
    (by rw [esp']; exact dKS.sub_right r8) (by rw [esp']; exact dPS.sub_right r8)
    (by rw [esp']; exact dWS.sub_right r8)) fun u ⟨hres, hesi, hedi, hesp, hrd, hwr, hsy, hfr⟩ => ⟨?_, ?_, ?_⟩)
  · exact hesp.trans esp'
  · rw [esp'] at hfr
    rw [hfr.readW (r := below (s.gpr .esp) 4) (Region.contains_self _ _) (fun r hr => ?_) (by decide), cm]
    · exact Mem.readW_writeW_self32 _ _ _
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact (dWS.sub_right r4).symm
      · rw [List.mem_singleton.mp hr]; exact d48
  · obtain U := Upd.setReg u .esp (s.gpr .esp)
    refine hQ _ (fun b hb => ?_) ((U.other _ (by decide)).trans hesi) ((U.other _ (by decide)).trans hedi) U.gpr
      (U.rd.trans hrd) (U.wr.trans hwr) (U.syms.trans hsy) ?_
    · rw [U.mem, hres b hb, st0_frame fc (fun r hr => by rw [List.mem_singleton.mp hr]; exact dWS) hb]
    · rw [U.mem]
      refine (fc.mono fun r hr => List.mem_cons_of_mem _ hr).trans (hfr.sub fun r hr => ?_)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · rw [List.mem_singleton.mp hr, esp']
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, r8⟩

/-! ## The modes' core -/

open VG.Proof.Modes.X86 (ScrIn coreRegion blkAddr blkRegion slotA stkRegion CoreSpec)
open VG.Proof.Blowfish (dirCipher dirCipher_len dirCipher_bytes bytesAt_eq dirBlock)
open VG.Spec.Aes (bytesAt)
open VG.Impl.Modes.X86 (sb)

/-- **The call, as the cipher of the core's sixteen blocks**: from the state
`s₁` with the entries of P in their order of use at `P`, which differs from
the core's state `s` in the copy's place at most. -/
theorem crypt_tail {s s₁ : State} {B S P : BitVec 32} {k : Schedule} {up : Bool} (hs : ScrIn s B 222)
    (hS : SchedAt s k S) (ha : Apart S (s.ea (at_ .esp 4)) s.wr)
    (dSK : Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨S.setWidth 64, 4168⟩)
    (dSA : Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨s.ea (at_ .esp 4), 4⟩)
    (dSB : Region.Disjoint (stkRegion (s.gpr .esp) 8) ⟨B.setWidth 64, 4 * 222⟩) (hsp : 8 ≤ (s.gpr .esp).toNat)
    (F : Fix16 S B P k (ord up) s₁) (hesi : s₁.gpr .esi = S) (hedi : s₁.gpr .edi = B) (hedx : s₁.gpr .edx = P)
    (hesp : s₁.gpr .esp = s.gpr .esp) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr)
    (hf : Frame [⟨slot B 768, 72⟩] s.mem s₁.mem)
    (dPS : Region.Disjoint ⟨P.setWidth 64, 72⟩ (below (s.gpr .esp) 8)) :
    WP isa (.call fnName cryptBlocks) s₁ fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Rdy 222 s' B k ∧
      Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem s'.mem ∧
      (∀ j < 16, bytesAt s'.mem (blkAddr (core16 up) B j) 8 =
        dirCipher up k (bytesAt s.mem (blkAddr (core16 up) B j) 8)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have scr : (⟨B.setWidth 64, 888⟩ : Region) ∈ s.wr := hs.wr
  have hfit : B.toNat + 888 ≤ 2 ^ 32 := hs.fit
  obtain aS := (ha _ scr).1
  obtain aA := (ha _ scr).2
  obtain coreSub : Region.Sub (coreRegion (core16 up) B) ⟨B.setWidth 64, 888⟩ :=
    Region.sub_prefix (show 4 * 212 ≤ 888 by decide)
  obtain wSub : Region.Sub (wR16 B) (coreRegion (core16 up) B) :=
    Offset.sub_base _ (show 64 + 704 ≤ 4 * 212 by decide)
  obtain pSub : Region.Sub ⟨slot B 768, 72⟩ (coreRegion (core16 up) B) :=
    Offset.sub_base _ (show 768 + 72 ≤ 4 * 212 by decide)
  refine call_wp F hesi hedi hedx (by rw [hesp]; exact hsp) (by rw [hesp]; exact dSK.symm) (by rw [hesp]; exact dPS)
    (by rw [hesp]; exact (dSB.sub_right (fun a h => coreSub a (wSub a h))).symm)
    fun u hres hesi' hedi' hesp' hrd' hwr' _ hfr => ?_
  rw [hesp] at hfr
  obtain FR : Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem u.mem :=
    (hf.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self, pSub⟩).trans
      (hfr.sub fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨_, List.mem_cons_self, wSub⟩
        · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩)
  obtain esp₄ : u.gpr .esp = s.gpr .esp := hesp'.trans hesp
  obtain rd₄ : u.rd = s.rd := hrd'.trans hrd
  obtain wr₄ : u.wr = s.wr := hwr'.trans hwr
  obtain apS : Apart S (s.ea (at_ .esp 4)) [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨aS.sub_right coreSub, aA.sub_right coreSub⟩
    · rw [List.mem_singleton.mp hr]; exact ⟨dSK.symm, dSA.symm⟩
  refine ⟨hedi', esp₄, ⟨S, hS.frame apS esp₄ rd₄ wr₄ FR, by rw [wr₄, ea_congr esp₄]; exact ha,
      by rw [esp₄]; exact dSK, by rw [esp₄, ea_congr esp₄]; exact dSA, by rw [esp₄]; exact dSB, hfit⟩,
    FR, fun j hj => ?_, rd₄, wr₄⟩
  obtain hba : blkAddr (core16 up) B j = slot B (bufOff + 8 * j) := by
    show B.setWidth 64 + BitVec.ofNat 64 (4 * 96) + BitVec.ofNat 64 (4 * 2 * j) = _
    rw [Offset.add_add, show 4 * 96 + 4 * 2 * j = bufOff + 8 * j by unfold bufOff; omega]
  rw [hba, dirCipher_bytes, bytesAt_eq, hres j hj, show dirBlock k up = VG.Proof.Blowfish.X86.blockOut k up from rfl,
    blockOut_eq, st0_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by decide) (by decide) (by decide)) hj]
  rfl

/-- While the decrypting core copies the entries of P in reverse: `i` of
them are in place. -/
structure PInv (s : State) (S B : BitVec 32) (SK : Schedule) (i : Nat) (u : State) : Prop where
  esi : u.gpr .esi = S
  gpr : ∀ r, r ≠ .eax → u.gpr r = s.gpr r
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [⟨slot B 768, 72⟩] s.mem u.mem
  pv : ∀ j < i, u.mem.readW (slot B (768 + 4 * j)) 32 = pEntry SK (17 - j)

/-- The entries `17 - i` to `18 - i - n` of P, to the places `i` to `i + n - 1` of the copy. -/
theorem revPs_wp {s : State} {S B : BitVec 32} {SK : Schedule} {is : List Instr} {Q : State → Prop}
    (hS : S.toNat + 4168 ≤ 2 ^ 32) (hBf : B.toNat + 888 ≤ 2 ^ 32) (hedi : s.gpr .edi = B)
    (rK : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (slot S o) n)
    (wB : ∀ d n, d + n ≤ 888 → InRegions s.wr (slot B d) n) (hk : scheduleAt s.mem (S.setWidth 64) = SK)
    (dKP : Region.Disjoint ⟨S.setWidth 64, 4168⟩ ⟨slot B 768, 72⟩) (n : Nat) :
    ∀ (i : Nat) (u : State), i + n ≤ 18 → PInv s S B SK i u →
      (∀ u', PInv s S B SK (i + n) u' → WP isa (.block is) u' Q) →
      WP isa (.block ((List.range' i n).flatMap revP ++ is)) u Q := by
  induction n with
  | zero => exact fun i u _ h k => k u h
  | succ n ih =>
    intro i u hn h k
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    show WP isa (.block (.mov .eax (.mem ⟨.esi, pOff + 4 * (17 - i)⟩) :: .store ⟨sb, prOff + 4 * i⟩ .eax :: _)) u _
    obtain aK : addr S (pOff + 4 * (17 - i)) = slot S (4096 + 4 * (17 - i)) :=
      addr_of_fit (by simp only [pOff]; omega)
    obtain aB : addr B (prOff + 4 * i) = slot B (768 + 4 * i) := addr_of_fit (by simp only [prOff]; omega)
    obtain hk' : scheduleAt u.mem (S.setWidth 64) = SK :=
      (scheduleAt_eq_of_frame _ h.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact dKP).trans hk
    refine wp_ldm h.esi (by rw [aK, h.rd, h.wr]; exact rK _ _ (by omega)) fun u₁ h₁ =>
      wp_stm (B := B) (by rw [h₁.other _ (by decide), h.gpr _ (by decide)]; exact hedi)
        (by rw [aB, h₁.wr, h.wr]; exact wB _ _ (by omega)) fun u₂ h₂ => ?_
    refine ih (i + 1) u₂ (by omega) ⟨by rw [h₂.gpr, h₁.other _ (by decide)]; exact h.esi,
      fun r hr => by rw [h₂.gpr, h₁.other r hr]; exact h.gpr r hr, by rw [h₂.rd, h₁.rd]; exact h.rd,
      by rw [h₂.wr, h₁.wr]; exact h.wr, ?_, fun j hj => ?_⟩
      fun u' h' => k u' ((show i + 1 + n = i + (n + 1) by omega) ▸ h')
    · rw [h₂.mem, h₁.mem, aB]
      exact h.frame.writeW List.mem_cons_self _ (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [h₂.mem, h₁.mem, aB]
      by_cases e : j = i
      · rw [e, Mem.readW_writeW_self32, h₁.gpr, aK, ← hk', pEntry_read _ _ (by omega)]
      · exact (Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)).trans
          (h.pv j (by omega))

/-- **The sixteen blocks of the core's buffer, encrypted (`up`) or decrypted
in place.** -/
theorem crypt_wp (up : Bool) {s : State} {B : BitVec 32} {k : Schedule} (hB : s.gpr sb = B) (hs : ScrIn s B 222)
    (hr : Rdy 222 s B k) (hsp : 8 ≤ (s.gpr .esp).toNat) :
    WP isa (crypt up) s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Rdy 222 s' B k ∧
      Frame [coreRegion (core16 up) B, stkRegion (s.gpr .esp) 8] s.mem s'.mem ∧
      (∀ j < 16, bytesAt s'.mem (blkAddr (core16 up) B j) 8 =
        dirCipher up k (bytesAt s.mem (blkAddr (core16 up) B j) 8)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨S, ⟨hin, hv, hk, hsch, hSfit⟩, ha, dSK, dSA, dSB, hfit⟩ := hr
  have hB' : s.gpr .edi = B := hB
  have scr : (⟨B.setWidth 64, 888⟩ : Region) ∈ s.wr := hs.wr
  have hfit' : B.toNat + 888 ≤ 2 ^ 32 := hfit
  obtain wB : ∀ d n, d + n ≤ 888 → InRegions s.wr (slot B d) n := fun d n h =>
    ⟨_, scr, Offset.contains_base _ (by omega) (by omega)⟩
  obtain rK : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (slot S o) n := fun o n h =>
    ⟨_, hsch, Offset.contains_base _ (by omega) (by omega)⟩
  obtain aS := (ha _ scr).1
  obtain dKW : Region.Disjoint ⟨S.setWidth 64, 4168⟩ (wR16 B) := aS.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ?_
  show WP isa (.block (.mov .esi (.mem ⟨.esp, 4⟩) :: pSetup up)) s _
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  obtain esi₁ : s₁.gpr .esi = S := u₁.gpr.trans hv
  cases up with
  | true =>
    show WP isa (.block [.mov .edx (.reg .esi), .alu .add .edx (imm pOff)]) s₁ _
    refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => WP.block_nil ?_
    obtain M : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    obtain RD : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
    obtain WR : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
    obtain G : ∀ r, r ≠ .esi → r ≠ .edx → s₃.gpr r = s.gpr r := fun r a b => by
      rw [u₃.other r b, u₂.other r b, u₁.other r a]
    obtain edx₃ : s₃.gpr .edx = S + BitVec.ofNat 32 4096 := by rw [u₃.gpr, u₂.gpr, esi₁]; rfl
    obtain eP : (S + BitVec.ofNat 32 4096).setWidth 64 = slot S 4096 := addr_of_fit (by omega)
    refine crypt_tail (up := true) (P := S + BitVec.ofNat 32 4096) hs ⟨hin, hv, hk, hsch, hSfit⟩ ha dSK dSA dSB hsp
      ⟨hSfit, by omega, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, by rw [RD, WR]; exact rK,
        fun o n _ h' => by rw [WR]; exact wB o n (by omega), fun o n h => ?_, dKW, ?_, by rw [M]; exact hk.symm,
        fun i hi => ?_⟩
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact esi₁) ((G _ (by decide) (by decide)).trans hB')
      edx₃ (G _ (by decide) (by decide)) RD WR (by rw [M]; exact Frame.refl _ _) ?_
    · rw [RD, WR]
      show InRegions _ ((S + BitVec.ofNat 32 4096).setWidth 64 + BitVec.ofNat 64 o) n
      rw [eP, Offset.add_add]; exact rK _ _ (by omega)
    · rw [eP]; exact dKW.sub_left (Offset.sub_base _ (by decide))
    · show s₃.mem.readW ((S + BitVec.ofNat 32 4096).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 = pEntry k i
      rw [eP, Offset.add_add, M, hk, pEntry_read _ _ hi]
    · rw [eP]; exact dSK.symm.sub_left (Offset.sub_base _ (by decide))
  | false =>
    show WP isa (.block ((List.range 18).flatMap revP ++
      [.mov .edx (.reg sb), .alu .add .edx (imm prOff)])) s₁ _
    rw [List.range_eq_range']
    obtain dKP : Region.Disjoint ⟨S.setWidth 64, 4168⟩ ⟨slot B 768, 72⟩ := aS.sub_right (Offset.sub_base _ (by decide))
    refine revPs_wp (s := s₁) (SK := k) hSfit hfit' ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact rK) (by rw [u₁.wr]; exact wB) (by rw [u₁.mem]; exact hk.symm) dKP 18 0 s₁
      (by decide) ⟨esi₁, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j h => absurd h (Nat.not_lt_zero _)⟩
      fun u h => ?_
    refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => WP.block_nil ?_
    obtain M : s₃.mem = u.mem := by rw [u₃.mem, u₂.mem]
    obtain RD : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, h.rd, u₁.rd]
    obtain WR : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, h.wr, u₁.wr]
    obtain G : ∀ r, r ≠ .esi → r ≠ .edx → r ≠ .eax → s₃.gpr r = s.gpr r := fun r a b c => by
      rw [u₃.other r b, u₂.other r b, h.gpr r c, u₁.other r a]
    obtain edi₃ : s₃.gpr .edi = B := (G _ (by decide) (by decide) (by decide)).trans hB'
    obtain edx₃ : s₃.gpr .edx = B + BitVec.ofNat 32 768 := by
      rw [u₃.gpr, u₂.gpr, h.gpr _ (by decide), u₁.other _ (by decide), hB]; rfl
    obtain eP : (B + BitVec.ofNat 32 768).setWidth 64 = slot B 768 := addr_of_fit (by omega)
    obtain hf : Frame [⟨slot B 768, 72⟩] s.mem s₃.mem := by
      have := h.frame
      rw [u₁.mem] at this
      rw [M]; exact this
    refine crypt_tail (up := false) (P := B + BitVec.ofNat 32 768) hs ⟨hin, hv, hk, hsch, hSfit⟩ ha dSK dSA dSB hsp
      ⟨hSfit, by omega, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega, by rw [RD, WR]; exact rK,
        fun o n _ h' => by rw [WR]; exact wB o n (by omega), fun o n h' => ?_, dKW, ?_,
        (scheduleAt_eq_of_frame _ hf fun r hr => by rw [List.mem_singleton.mp hr]; exact dKP).trans hk.symm,
        fun i hi => ?_⟩
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact h.esi) edi₃ edx₃
      (G _ (by decide) (by decide) (by decide)) RD WR hf ?_
    · rw [RD, WR]
      show InRegions _ ((B + BitVec.ofNat 32 768).setWidth 64 + BitVec.ofNat 64 o) n
      rw [eP, Offset.add_add]
      obtain ⟨r, hr, hc⟩ := wB (768 + o) n (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [eP]; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · show s₃.mem.readW ((B + BitVec.ofNat 32 768).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 = pEntry k (17 - i)
      rw [eP, Offset.add_add, M]; exact h.pv i hi
    · rw [eP]; exact dSB.symm.sub_left (Offset.sub_base _ (by decide))

/-- **The sixteen-block core by `pshufb` meets what the modes need**, in
either direction, with nothing to prepare. -/
def wideCoreSpec (up : Bool) : CoreSpec (core16 up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := KeyArgsN 8
  Ready := Rdy 222
  cipher_len _ _ := dirCipher_len _ _ _
  layout := ⟨show 0 < 16 by decide, .inl rfl, show 96 + 2 * 16 ≤ 212 by decide, show 212 + 10 ≤ 222 by decide⟩
  keyArgs_congr h e r w _ f := keyArgsN_congr h e r w f
  ready_frame h e r w _ hf hs _ := rdy_frame h e r w hf hs
  prepare_wp hB hs hR hk _ := by
    obtain ⟨⟨S, hS, -, hw⟩, hsr, hsk, hsa⟩ := hk
    obtain e : arg _ 0 = S := hS.2.1
    rw [e] at hsk
    exact WP.block_nil ⟨⟨S, hS, hw, hsk, hsa, hsr _ hR, hs.fit⟩, hB, rfl, Frame.refl _ _, rfl, rfl⟩
  crypt_wp hB hs hr hsp := crypt_wp up hB hs hr hsp

/-- It fits Blowfish's functions, with 111 words of working space and eight
bytes of stack. -/
def wideFits (up : Bool) : Fits (wideCoreSpec up) 111 8 := ⟨id, id, rfl, rfl, rfl, rfl⟩

end VG.Proof.Blowfish.X86.Ssse3.Wide
