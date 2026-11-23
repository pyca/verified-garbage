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
* `planes_wp`: xL after the round's entry of P, and the four registers of
  its bytes;
* `sbox_wp`: an S-box's entries of the sixteen blocks, into F.
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

end VG.Proof.Blowfish.X86.Ssse3.Wide
