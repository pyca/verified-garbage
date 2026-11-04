module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifySpec
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkVerified
public import VerifiedGarbage.Proof.MdHashTable.AArch64
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCEnc
import VerifiedGarbage.Proof.HashTable.AArch64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.RsaPss.AArch64.SignSpec

/-!
# RSASSA-PSS verification on AArch64, around the check of the encoding: its call

After the public-key operation (`AfterCall`), `chkArgs` sets `x26` to 1 if
`lo = 0` or RSAVP1's first byte is zero, and `checkEncoding`'s arguments:
the last `emLen` bytes of RSAVP1's output, the working space from the next
multiple of 8, and the tables' addresses on the stack (`chkArgs_ok`,
`AtChkC`), which meet its contract for the functions the tables name
(`CSel`, `chkPre_of`); after the call of `checkEncoding` for the table's
index, `x0` says whether the encoding is consistent (`chkCall_ok`,
`AfterChkC`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_add wp_sub wp_addImm wp_subImm wp_movz wp_and wp_lsr wp_lsl
  wp_ldrb wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov wp_addSp)
open VG.Proof.RsaPss.AArch64 (off stkR shr3_ofNat shl3_ofNat Tabs TabsAt held_frame)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR kb fb fb_eq frame_sub frame_sub0 below_sub in_frame stackArgAddr_fb
  stackArgAddr_eq below_kR)

/-- The working space's words that RSAVP1's output takes. -/
abbrev cwV (s : State) : Nat := ((s.gpr .x1).toNat + 7) / 8

/-- The flag: `lo = 0`, or the leading byte zero. -/
theorem flag_eq (b : Byte) {lo : Nat} (hlo : lo ≤ 1) :
    ((b.setWidth 64 &&& ((BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 lo)) - BitVec.ofNat 64 1) >>> 63 =
      if lo = 0 ∨ b = 0 then 1 else 0 := by
  rcases (by omega : lo = 0 ∨ lo = 1) with rfl | rfl
  · simp
  · have e : ((BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 1 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    by_cases h : b = 0
    · subst h; decide
    · have h' : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      rw [ite_eq_right fun h1 => h1.elim (by omega) h]
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega

/-- At the call of `checkEncoding`, but for the tables. -/
structure AtChkC0 (K : Nat) (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [kR K s, sR s] s.mem t.mem
  fr : Fr s t.mem
  res : Cons s → Spec.Rsa.bytesAt t.mem (scr s) (s.gpr .x1).toNat = pubX s
  x0 : t.gpr .x0 = s.gpr .x4
  x1 : t.gpr .x1 = off (scr s) (loS s)
  x2 : t.gpr .x2 = BitVec.ofNat 64 (elS s)
  x3 : t.gpr .x3 = BitVec.ofNat 64 (ebS s)
  x4 : t.gpr .x4 = stackArg s 0
  x5 : t.gpr .x5 = anyV s
  x6 : t.gpr .x6 = off (scr s) (8 * cwV s)
  x7 : t.gpr .x7 = stackArg s 3 - BitVec.ofNat 64 (cwV s)
  x26 : t.gpr .x26 = if loS s = 0 ∨ t.mem (scr s) = 0 then 1 else 0
  x27 : t.gpr .x27 = s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64

/-- At the call of `checkEncoding`: and the tables' addresses its stack arguments. -/
structure AtChkC (K : Nat) (s t : State) : Prop extends AtChkC0 K s t where
  a0 : stackArg t 0 = stackArg s 6
  a1 : stackArg t 1 = stackArg s 7

/-- `chkArgs` without the tables' addresses, and those. -/
abbrev chkArgsA : List Instr :=
  [.add .x .x1 .x20 .x26, .ldrb .x9 .x20 0, movi .x10 0, .sub .x .x10 .x10 .x26, .logic .and .x .x9 .x9 .x10,
    .subImm .x .x26 .x9 1, .lsr .x .x26 .x26 63,
    ld .x0 sDig, VG.Impl.MdStream.AArch64.mov .x2 .x25, VG.Impl.MdStream.AArch64.mov .x3 .x24, ld .x4 sSaltLen,
    ld .x5 sAny, .addImm .x .x9 .x23 7, .lsr .x .x9 .x9 3, ld .x7 sScrLen, .sub .x .x7 .x7 .x9, .lsl .x .x9 .x9 3,
    .add .x .x6 .x20 .x9]
abbrev tabArgsV : List Instr := [.addSp .x16 0, arg .x9 6, .str .x .x9 .x16 0, arg .x9 7, .str .x .x9 .x16 8]

theorem chkArgs_eq : chkArgs = chkArgsA ++ tabArgsV := rfl

theorem written_getD {m : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m out n r o) : Spec.Rsa.bytesAt m out n = o.getD (Spec.RsaPss.zeros n) := by
  cases o with
  | none => exact h.2
  | some x => exact h.2

theorem chkArgsA_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreV tsH tsG K s)
    (h0 : s.mem (s.gpr .x0) ≠ 0) (ha : AfterCall K s (ebS s) (elS s) (loS s) t) :
    WP isa (.block chkArgsA) t (AtChkC0 K s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, -, hlo⟩ := eb_bounds hk1 hk2 h0
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)))
  unfold chkArgsA ld movi
  refine wp_add fun u₁ o₁ e₁ => wp_ldrb (by decide) (a := scr s) (by rw [o₁.get .x20, ha.x20, BitVec.add_zero])
    (by
      rw [o₁.rd, o₁.wr, ha.rd, ha.wr]
      have hc := Offset.contains_base (scr s) (d := 0) (n := 1) (k := (stackArg s 3).toNat * 8)
        (by have := hp.hs; omega_arith) (by decide)
      rw [BitVec.add_zero] at hc
      exact InRegions_append_cons.mpr (.inr ⟨sR s, List.mem_append_right _ hp.hws, hc⟩))
    fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_sub fun u₄ o₄ e₄ => wp_and fun u₅ o₅ e₅ =>
    wp_subImm (by decide) fun u₆ o₆ e₆ => wp_lsr (by decide) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x1, .x9, .x10, .x26] t u₇ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans
    (o₆.trans o₇)))))).mono
  have x26₇ : u₇.gpr .x26 = if loS s = 0 ∨ t.mem (scr s) = 0 then 1 else 0 := by
    rw [e₇, e₆, e₅, e₄, e₃, o₃.get .x26, o₂.get .x26, o₁.get .x26, ha.x26, o₄.get .x9, o₃.get .x9, e₂,
      o₁.mem, flag_eq _ hlo]
  have sp₇ : u₇.sp = fb s := by rw [O₇.sp, ha.sp]
  have rd₇ : u₇.rd = s.rd := by rw [O₇.rd, ha.rd]
  have wr₇ : u₇.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₇.wr, ha.wr]
  have mem₇ : u₇.mem = t.mem := O₇.mem
  refine wp_ldrSp (by decide) (rsl sp₇ rd₇ wr₇ (by decide)) fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ =>
    wp_mov fun u₁₀ o₁₀ e₁₀ => ?_
  have sp₁₀ : u₁₀.sp = fb s := by rw [o₁₀.sp, o₉.sp, o₈.sp, sp₇]
  have rd₁₀ : u₁₀.rd = s.rd := by rw [o₁₀.rd, o₉.rd, o₈.rd, rd₇]
  have wr₁₀ : u₁₀.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₀.wr, o₉.wr, o₈.wr, wr₇]
  have mem₁₀ : u₁₀.mem = t.mem := by rw [o₁₀.mem, o₉.mem, o₈.mem, mem₇]
  refine wp_ldrSp (by decide) (rsl sp₁₀ rd₁₀ wr₁₀ (by decide)) fun u₁₁ o₁₁ e₁₁ => ?_
  refine wp_ldrSp (by decide) (by rw [o₁₁.sp, o₁₁.rd, o₁₁.wr]; exact rsl sp₁₀ rd₁₀ wr₁₀ (by decide))
    fun u₁₂ o₁₂ e₁₂ => wp_addImm (by decide) fun u₁₃ o₁₃ e₁₃ => wp_lsr (by decide) fun u₁₄ o₁₄ e₁₄ => ?_
  have sp₁₄ : u₁₄.sp = fb s := by rw [o₁₄.sp, o₁₃.sp, o₁₂.sp, o₁₁.sp, sp₁₀]
  have rd₁₄ : u₁₄.rd = s.rd := by rw [o₁₄.rd, o₁₃.rd, o₁₂.rd, o₁₁.rd, rd₁₀]
  have wr₁₄ : u₁₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₄.wr, o₁₃.wr, o₁₂.wr, o₁₁.wr, wr₁₀]
  have mem₁₄ : u₁₄.mem = t.mem := by rw [o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem, mem₁₀]
  refine wp_ldrSp (by decide) (rsl sp₁₄ rd₁₄ wr₁₄ (by decide)) fun u₁₅ o₁₅ e₁₅ => wp_sub fun u₁₆ o₁₆ e₁₆ =>
    wp_lsl (by decide) fun u₁₇ o₁₇ e₁₇ => wp_add fun u₁₈ o₁₈ e₁₈ => wp_nil ?_
  have O : Only [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x9] u₇ u₁₈ :=
    (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans
      (o₁₇.trans o₁₈)))))))))).mono
  have x9₁₄ : u₁₄.gpr .x9 = BitVec.ofNat 64 (cwV s) := by
    rw [e₁₄, e₁₃, o₁₂.get .x23, o₁₁.get .x23, o₁₀.get .x23, o₉.get .x23, o₈.get .x23, O₇.get .x23, ha.x23,
      ← (BitVec.ofNat_toNat 64 (s.gpr .x1)).trans (BitVec.setWidth_eq _), BitVec.ofNat_add_ofNat,
      shr3_ofNat (by omega)]
  have hcw : cwV s < 2 ^ 60 := by unfold cwV; omega
  have F := ha.fr
  rw [sp₇, mem₇, F.rs (.x4, sDig) (by simp [regSlots])] at e₈
  rw [sp₁₀, mem₁₀, F.sl] at e₁₁
  rw [o₁₁.sp, sp₁₀, o₁₁.mem, mem₁₀, F.any] at e₁₂
  rw [sp₁₄, mem₁₄, F.scr] at e₁₅
  have mem : u₁₈.mem = t.mem := by rw [O.mem, mem₇]
  exact {
    sp := by rw [O.sp, sp₇]
    rd := by rw [O.rd, rd₇]
    wr := by rw [O.wr, wr₇]
    v := fun r hr => by rw [O.vcs r hr, O₇.vcs r hr, ha.v r hr]
    mem := by rw [mem]; exact ha.mem
    fr := by rw [mem]; exact F
    res := fun hc => by rw [mem]; exact written_getD (ha.res hc)
    x0 := by
      rw [o₁₈.get .x0, o₁₇.get .x0, o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0,
        o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, e₈]
    x1 := by
      rw [O.get .x1, o₇.get .x1, o₆.get .x1, o₅.get .x1, o₄.get .x1, o₃.get .x1, o₂.get .x1, e₁, ha.x20, ha.x26]
    x2 := by
      rw [o₁₈.get .x2, o₁₇.get .x2, o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, o₁₃.get .x2, o₁₂.get .x2,
        o₁₁.get .x2, o₁₀.get .x2, e₉, o₈.get .x25, O₇.get .x25, ha.x25]
    x3 := by
      rw [o₁₈.get .x3, o₁₇.get .x3, o₁₆.get .x3, o₁₅.get .x3, o₁₄.get .x3, o₁₃.get .x3, o₁₂.get .x3,
        o₁₁.get .x3, e₁₀, o₉.get .x24, o₈.get .x24, O₇.get .x24, ha.x24]
    x4 := by
      rw [o₁₈.get .x4, o₁₇.get .x4, o₁₆.get .x4, o₁₅.get .x4, o₁₄.get .x4, o₁₃.get .x4, o₁₂.get .x4, e₁₁]
    x5 := by rw [o₁₈.get .x5, o₁₇.get .x5, o₁₆.get .x5, o₁₅.get .x5, o₁₄.get .x5, o₁₃.get .x5, e₁₂]
    x6 := by
      rw [e₁₈, o₁₇.get .x20, o₁₆.get .x20, o₁₅.get .x20, o₁₄.get .x20, o₁₃.get .x20, o₁₂.get .x20,
        o₁₁.get .x20, o₁₀.get .x20, o₉.get .x20, o₈.get .x20, O₇.get .x20, ha.x20, e₁₇, o₁₆.get .x9,
        o₁₅.get .x9, x9₁₄, shl3_ofNat hcw]
    x7 := by rw [o₁₈.get .x7, o₁₇.get .x7, e₁₆, e₁₅, o₁₅.get .x9, x9₁₄]
    x26 := by rw [O.get .x26, x26₇, mem]
    x27 := by rw [O.get .x27, O₇.get .x27, ha.x27] }

/-- A stack argument, in memory changed only in the stack we use and our working space. -/
theorem arg_frameV {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) {m : Mem}
    (h : Frame [kR K s, sR s] s.mem m) {j : Nat} (hj : j < 8) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (r := aR s) (by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.ka.symm
      · exact hp.sa.symm) (by decide)

/-- The tables' addresses to the stack arguments of `checkEncoding`. -/
theorem tabArgsV_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreV tsH tsG K s)
    (ha : AtChkC0 K s t) : WP isa (.block tabArgsV) t (AtChkC K s) := by
  have hA : ∀ {u : State} (j : Nat), j < 8 → u.sp = fb s → u.rd = s.rd →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8 := fun j hj hsp hrd => by
    rw [hsp, hrd, ← stackArgAddr_fb]; exact arg_in hp (Covers.left (Covers.refl _)) hj
  have hk2 := hp.k2; have hhs := hp.hs
  unfold tabArgsV arg
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_ldrSp (by decide) (hA 6 (by decide) (by rw [o₁.sp, ha.sp]) (by rw [o₁.rd, ha.rd]))
    fun u₂ o₂ e₂ => ?_
  rw [o₁.sp, ha.sp, ← stackArgAddr_fb, o₁.mem, arg_frameV hp ha.mem (by decide)] at e₂
  refine wp_strx (a := fb s + BitVec.ofNat 64 0) (by decide) (by rw [o₂.get .x16, e₁])
    (by rw [o₂.wr, o₁.wr, ha.wr]; exact in_frame s _ (by decide)) fun u₃ m₃ => ?_
  refine wp_ldrSp (by decide) (hA 7 (by decide) (by rw [m₃.sp, o₂.sp, o₁.sp, ha.sp])
    (by rw [m₃.rd, o₂.rd, o₁.rd, ha.rd])) fun u₄ o₄ e₄ => ?_
  have hm₃ : u₃.mem = t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 6) := by
    rw [m₃.mem, o₂.mem, o₁.mem, e₂]
  have hK16 : Region.Sub ⟨fb s + BitVec.ofNat 64 0, 16⟩ (kR K s) := frame_sub K s (by decide)
  have f₃ : Frame [kR K s, sR s] s.mem u₃.mem := by
    rw [hm₃]
    have hsp := hp.sp1
    have hlt := s.sp.isLt
    exact ha.mem.writeW (r := kR K s) (by simp) _ (by
      rw [Sgn.off_fb K s 0]; exact Offset.contains_base _ (by unfold stk frameBytes; omega) (by unfold stk at hsp; omega))
  rw [m₃.sp, o₂.sp, o₁.sp, ha.sp, ← stackArgAddr_fb, arg_frameV hp f₃ (by decide)] at e₄
  refine wp_strx (a := fb s + BitVec.ofNat 64 8) (by decide) (by rw [o₄.get .x16, m₃.gpr, o₂.get .x16, e₁])
    (by rw [o₄.wr, m₃.wr, o₂.wr, o₁.wr, ha.wr]; exact in_frame s _ (by decide)) fun u₅ m₅ => wp_nil ?_
  have hm₅ : u₅.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 6)).writeW (fb s + BitVec.ofNat 64 8)
      (stackArg s 7) := by rw [m₅.mem, o₄.mem, hm₃, e₄]
  have hf : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] t.mem u₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have K₅ : Keep [.x16, .x9] t u₅ := (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans m₅.keep)))).mono
  have g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x26, .x27],
      u₅.gpr r = t.gpr r := fun r hr => K₅.get r (by revert r; decide)
  have sp₅ : u₅.sp = fb s := K₅.sp.trans ha.sp
  have hd16 : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)],
      (frA s).Disjoint r ∧ (frB s).Disjoint r ∧ (frC s).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (by decide) (by decide) (by decide), Offset.disjoint _ (by decide) (by decide) (by decide),
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  -- Our working space is apart from the 16 bytes written.
  have hsd : ∀ {p : Addr} {n : Nat}, Region.Sub ⟨p, n⟩ (sR s) → n < 2 ^ 64 → ∀ i < n,
      u₅.mem (p + BitVec.ofNat 64 i) = t.mem (p + BitVec.ofNat 64 i) := fun hS hn i hi => by
    refine hf _ fun r hr hc => ?_
    rw [List.mem_singleton.mp hr] at hc
    exact (hp.ks.sub_left hK16).sub_right hS _ hc (Offset.contains_base _ (by omega) (by omega))
  have hS1 : Region.Sub ⟨scr s, (s.gpr .x1).toNat⟩ (sR s) := Region.sub_prefix (by omega)
  have hb : Spec.Rsa.bytesAt u₅.mem (scr s) (s.gpr .x1).toNat = Spec.Rsa.bytesAt t.mem (scr s) (s.gpr .x1).toNat := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => hsd hS1 (by omega) i (List.mem_range.mp hi)
  have h0m : u₅.mem (scr s) = t.mem (scr s) := by
    have := hsd hS1 (by omega) 0 (by have := hp.k1; omega)
    rwa [BitVec.add_zero] at this
  exact {
    sp := sp₅
    rd := K₅.rd.trans ha.rd
    wr := K₅.wr.trans ha.wr
    v := fun r hr => (K₅.vcs r hr).trans (ha.v r hr)
    mem := ha.mem.trans (hf.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨kR K s, by simp, hK16⟩)
    fr := ha.fr.frame hf (fun r hr => (hd16 r hr).1) (fun r hr => (hd16 r hr).2.1) (fun r hr => (hd16 r hr).2.2)
    res := fun hc => by rw [hb]; exact ha.res hc
    x0 := (g _ (by simp)).trans ha.x0
    x1 := (g _ (by simp)).trans ha.x1
    x2 := (g _ (by simp)).trans ha.x2
    x3 := (g _ (by simp)).trans ha.x3
    x4 := (g _ (by simp)).trans ha.x4
    x5 := (g _ (by simp)).trans ha.x5
    x6 := (g _ (by simp)).trans ha.x6
    x7 := (g _ (by simp)).trans ha.x7
    x26 := by rw [g _ (by simp), ha.x26, h0m]
    x27 := (g _ (by simp)).trans ha.x27
    a0 := by
      show u₅.mem.readW (u₅.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
      rw [hm₅, sp₅, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    a1 := by
      show u₅.mem.readW (u₅.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
      rw [hm₅, sp₅, Mem.readW_writeW_self64] }

theorem chkArgs_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreV tsH tsG K s)
    (h0 : s.mem (s.gpr .x0) ≠ 0) (ha : AfterCall K s (ebS s) (elS s) (loS s) t) :
    WP isa (.block chkArgs) t (AtChkC K s) := by
  rw [chkArgs_eq, WP.block_append_iff]
  exact WP.mono (chkArgsA_ok hp h0 ha) fun u hu => tabArgsV_ok hp hu

/-- `AtChkC` after the comparisons of the index, which write only `x9`. -/
theorem AtChkC.only9 {K : Nat} {s t t' : State} (h : AtChkC K s t) (o : Only [.x9] t t') : AtChkC K s t' where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  v := fun r hr => (o.vcs r hr).trans (h.v r hr)
  mem := o.mem ▸ h.mem
  fr := o.mem ▸ h.fr
  res := o.mem ▸ h.res
  x0 := (o.get .x0).trans h.x0
  x1 := (o.get .x1).trans h.x1
  x2 := (o.get .x2).trans h.x2
  x3 := (o.get .x3).trans h.x3
  x4 := (o.get .x4).trans h.x4
  x5 := (o.get .x5).trans h.x5
  x6 := (o.get .x6).trans h.x6
  x7 := (o.get .x7).trans h.x7
  x26 := by rw [o.get .x26, o.mem]; exact h.x26
  x27 := (o.get .x27).trans h.x27
  a0 := by show t'.mem.readW _ 64 = _; rw [o.mem, stackArgAddr, o.sp]; exact h.a0
  a1 := by show t'.mem.readW _ 64 = _; rw [o.mem, stackArgAddr, o.sp]; exact h.a1

theorem cw_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreV tsH tsG K s) :
    (stackArg s 3 - BitVec.ofNat 64 (cwV s)).toNat = (stackArg s 3).toNat - cwV s := by
  have := hp.hs; have := hp.k2
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 3).isLt
  unfold cwV at *
  omega

/-- What the tables at the stack arguments 6 and 7 of `s` give the call of
`checkEncoding` for the index `i` of the table of `MdHash`: the tables of
the precondition that they are, the functions `T` of both tables, the hash
functions `Hs` and `Gs` they name, and that `checkEncoding` for the index
`i` computes the check with them. -/
structure CSel (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (s : State) (i : Nat)
    (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Prop where
  mem : i ∈ idxs
  idx : s.mem.readW (stackArg s 6 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i
  eH : T.tsH = tsH
  eG : T.tsG = tsG
  selH : ∃ TH ∈ tsH, (FnTable.words isa s TH).length = 11 ∧
    Abi.tableHeld 64 s.mem (stackArg s 6) (FnTable.words isa s TH)
  selG : ∃ TG ∈ tsG, (FnTable.words isa s TG).length = 5 ∧
    Abi.tableHeld 64 s.mem (stackArg s 7) (FnTable.words isa s TG)
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 6) (stackArg s 7) s
  hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 6) = some Hs
  hG : Spec.HashTable.hashAt 64 s.mem (stackArg s 7) = some Gs
  hD : T.H.D = (s.gpr .x5).toNat
  hl : Hs.len = T.H.D
  ok : ∀ s', (Chk.chkK T Hs Gs).pre s' → ∃ t s'', Exec isa (checkEncoding f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Chk.chkK T Hs Gs).post s' s''
  depth : (checkEncoding f (ofIdx i) g).aarch64Depth ≤ 39

/-- The regions a call of `checkEncoding` reads and writes. -/
abbrev chkRdT (D : Nat) (t : State) : List Region :=
  [⟨t.gpr .x0, D⟩, ⟨t.gpr .x1, (t.gpr .x2).toNat⟩, Sig.tableRegion 64 (stackArg t 0) 11,
    Sig.tableRegion 64 (stackArg t 1) 5, ⟨stackArgAddr t 0, 16⟩]
abbrev chkWrT (t : State) : List Region := [⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩]

/-- The call's arguments meet `checkEncoding`'s contract. -/
theorem chkPre_of {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} {K : Nat}
    {s t : State} (hp : PreV tsH tsG K s) (h624 : 624 ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (h0 : s.mem (s.gpr .x0) ≠ 0) (ha : AtChkC K s t)
    (hsy : t.syms = s.syms) :
    (Chk.chkK T Hs Gs).pre (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hsp1 := hp.sp1
  have hws : (scr s).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  have hsc := cw_toNat hp
  obtain ⟨hb1, hb2, hlok, hlo⟩ := eb_bounds hk1 hk2 h0
  have hcw : (s.gpr .x1).toNat ≤ 8 * cwV s ∧ 8 * cwV s ≤ (s.gpr .x1).toNat + 7 := by unfold cwV; omega
  have hK := below_kR (K := K) (cK := stk 288) s (by unfold stk frameBytes; omega)
  have hSem : Region.Sub ⟨off (scr s) (loS s), elS s⟩ (sR s) := Offset.sub_base _ (by omega)
  have hSsc : Region.Sub ⟨off (scr s) (8 * cwV s), (stackArg s 3 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have hA : Region.Sub ⟨fb s + BitVec.ofNat 64 (8 * 0), 16⟩ (kR K s) := frame_sub K s (by decide)
  have he : (BitVec.ofNat 64 (elS s)).toNat = elS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show elS s < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 (ebS s)).toNat = ebS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ebS s < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hwem : (off (scr s) (loS s)).toNat + elS s ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hwsc : (off (scr s) (8 * cwV s)).toNat + (stackArg s 3 - BitVec.ofNat 64 (cwV s)).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; omega
  have hD := E.hD
  have dH : ∀ r ∈ [kR K s, sR s], Region.Disjoint ⟨stackArg s 6, 88⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ktH.symm
    · exact hp.stH.symm
  have dG : ∀ r ∈ [kR K s, sR s], Region.Disjoint ⟨stackArg s 7, 40⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ktG.symm
    · exact hp.stG.symm
  have hsc0 : (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)).syms = s.syms := hsy
  have hm0 : (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)).mem = t.mem := rfl
  have hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7],
      (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)).gpr r = t.gpr r := by
    intro r hr; simp only [State.withRegions_gpr, State.callEntry]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have a0 : stackArg (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)) 0 = stackArg s 6 := ha.a0
  have a1 : stackArg (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)) 1 = stackArg s 7 := ha.a1
  have sp0 : (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)).sp = fb s := ha.sp
  have aA : stackArgAddr (t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)) 0 =
      fb s + BitVec.ofNat 64 (8 * 0) := by
    rw [stackArgAddr, sp0]
  have hsy' : ∀ x : State, x.syms = s.syms → ∀ T' : FnTable, FnTable.words isa x T' = FnTable.words isa s T' :=
    fun x hx T' => VG.Proof.HashTable.AArch64.words_congr hx T'
  refine ⟨⟨?sp1, ?sp2, ?tabH, ?tabG, ?hsy, rfl, rfl, ?ds, ?es, ?stH, ?stG, ?sA, ?kd, ?ke, ?ks, ?ktH, ?ktG, ?kA,
    ?wd, ?we, ?ws, ?wtH, ?wtG, ?b1, ?b2, ?hel, ?hs⟩, ?tabs⟩
  all_goals try simp only [Chk.dgR, Chk.emR, Chk.sR, Chk.tHR, Chk.tGR, Chk.aR, Sgn.kR,
    hg .x0 (by simp), hg .x1 (by simp), hg .x2 (by simp), hg .x3 (by simp),
    hg .x6 (by simp), hg .x7 (by simp), a0, a1, aA, sp0, ha.x0, ha.x1, ha.x2, ha.x3, ha.x6, ha.x7, he, hb]
  case sp1 => unfold Chk.chkStack stk frameBytes at *; omega
  case sp2 => omega
  case tabH =>
    obtain ⟨TH, mH, lH, heldH⟩ := E.selH
    refine ⟨TH, E.eH ▸ mH, ?_⟩
    rw [hsy' _ hsc0, hm0]
    exact held_frame ha.mem (by simpa using dH) (by decide) lH heldH
  case tabG =>
    obtain ⟨TG, mG, lG, heldG⟩ := E.selG
    refine ⟨TG, E.eG ▸ mG, ?_⟩
    rw [hsy' _ hsc0, hm0]
    exact held_frame ha.mem (by simpa using dG) (by decide) lG heldG
  case hsy => rw [hsc0, E.eH, E.eG]; exact hp.hsy
  case ds => rw [hD]; exact hp.dgs.sub_right hSsc
  case es => exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by rw [hsc]; omega)
  case stH => exact hp.stH.sub_left hSsc
  case stG => exact hp.stG.sub_left hSsc
  case sA => exact ((hp.ks.sub_left hA).sub_right hSsc).symm
  case kd => rw [hD]; exact hp.kdg.sub_left hK
  case ke => exact (hp.ks.sub_left hK).sub_right hSem
  case ks => exact (hp.ks.sub_left hK).sub_right hSsc
  case ktH => exact hp.ktH.sub_left hK
  case ktG => exact hp.ktG.sub_left hK
  case kA =>
    rw [show fb s + BitVec.ofNat 64 (8 * 0) = fb s from BitVec.add_zero _]
    exact (Offset.base_disjoint_below (fb s) (n := stk 288) (k := 16) (by unfold stk frameBytes; omega)).symm
  case wd => rw [hD]; exact hp.wdg
  case we => exact hwem
  case ws => exact hwsc
  case wtH => exact hp.wtH
  case wtG => exact hp.wtG
  case b1 => exact hb1
  case b2 => exact hb2
  case hs => rw [hsc]; unfold Proof.RsaPss.encScratch cwV at *; omega
  case tabs =>
    show TabsAt T.H T.dn T.f T.G T.g (stackArg _ 0) (stackArg _ 1) _
    rw [a0, a1]
    exact E.tabs.frame (t := t.callEntry.withRegions (chkRdT T.H.D t) (chkWrT t)) ha.mem dH dG hsc0

variable (Hs Gs : Spec.Mgf1.Hash) in
/-- After `checkEncoding`. -/
structure AfterChkC (K : Nat) (s t : State) : Prop extends Mid s t where
  mem : Frame [kR K s, sR s] s.mem t.mem
  x26 : Cons s → t.gpr .x26 = if loS s = 0 ∨ (pubX s).getD 0 0 = 0 then 1 else 0
  x0 : Cons s → (t.gpr .x0).setWidth 32 = if Spec.RsaPss.verifyEncoding Hs Gs
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) Hs.len) ((pubX s).drop (loS s)) (ebS s) (sLenV s) then 1 else 0

theorem bytesAt_drop (m : Mem) (p : Addr) {k lo : Nat} :
    (Spec.Rsa.bytesAt m p k).drop lo = Spec.Rsa.bytesAt m (off p lo) (k - lo) := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range, off, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

theorem chkCall_ok {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} {K : Nat}
    {s t : State} (hp : PreV tsH tsG K s) (h624 : 624 ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : CSel f g tsH tsG s i T Hs Gs) (h0 : s.mem (s.gpr .x0) ≠ 0) (ht : AtChkC K s t)
    (hsy : t.syms = s.syms) :
    WP isa (.call (chkName i) (checkEncoding f (ofIdx i) g)) t (AfterChkC Hs Gs K s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, hb2, hlok, -⟩ := eb_bounds hk1 hk2 h0
  have hd := E.depth
  have hcw : (s.gpr .x1).toNat ≤ 8 * cwV s ∧ 8 * cwV s ≤ (s.gpr .x1).toNat + 7 := by unfold cwV; omega
  have hsc := cw_toNat hp
  have hhs := hp.hs
  have hws : (scr s).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have he : (BitVec.ofNat 64 (elS s)).toNat = elS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show elS s < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 (ebS s)).toNat = ebS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ebS s < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hSem : Region.Sub ⟨off (scr s) (loS s), elS s⟩ (sR s) := Offset.sub_base _ (by omega)
  have hSsc : Region.Sub ⟨off (scr s) (8 * cwV s), (stackArg s 3 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have hcr : Covers (chkRdT T.H.D t) (t.rd ++ t.wr) := by
    simp only [chkRdT, ht.x0, ht.x1, ht.x2, ht.a0, ht.a1, E.hD, he]
    rw [ht.rd, ht.wr]
    have hm : ∀ r ∈ [dgR s, tHR s, tGR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h <;> simp [h]) hp.hrd)
    exact Covers.cons (hm _ (by simp)) (Covers.cons (Covers.right (Covers.one ⟨sR s,
      List.mem_cons_of_mem _ hp.hws, Offset.contains_base _ (by omega) (by omega)⟩))
      (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.right (Covers.one (by
        rw [stackArgAddr, ht.sp]; exact in_frame s s.wr (d := 8 * 0) (n := 16) (by decide)))))))
  have hcw' : Covers (chkWrT t) t.wr := by
    simp only [chkWrT, ht.x6, ht.x7]
    rw [ht.wr]
    exact Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws, Offset.contains_base _ (by rw [hsc]; omega)
      (by omega)⟩
  refine WP.callFV (k := Chk.chkK T Hs Gs) E.ok (chkPre_of hp h624 E h0 ht hsy)
    (Covers.append_left hcr (Covers.right hcw')) hcw' ?_ (by omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  have hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5], t.callEntry.gpr r = t.gpr r := by
    intro r hr; simp only [State.callEntry]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [Chk.chkK, Chk.chkOut, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    hg .x0 (by simp), hg .x1 (by simp), hg .x2 (by simp), hg .x3 (by simp), hg .x4 (by simp), hg .x5 (by simp),
    ht.x0, ht.x1, ht.x2, ht.x3, ht.x4, ht.x5, he, hb] at hpost
  simp only [chkWrT] at hf
  rw [ht.x6, ht.x7, ht.sp] at hf
  have hB : Region.Sub (below (fb s) (16 * (checkEncoding f (ofIdx i) g).aarch64Depth)) (kR K s) := fun a h =>
    below_sub K s a (Offset.sub_below (fb s) (a := 16 * (checkEncoding f (ofIdx i) g).aarch64Depth) (b := K)
      (n := 16 * (checkEncoding f (ofIdx i) g).aarch64Depth) (m := K) (by omega) (by omega) a h)
  have hA : ∀ {d n : Nat}, d + n ≤ frameBytes → ∀ r ∈ [(⟨off (scr s) (8 * cwV s),
      (stackArg s 3 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ : Region)] ++
        [below (fb s) (16 * (checkEncoding f (ofIdx i) g).aarch64Depth)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := fun hdn r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.ks.sub_left (frame_sub K s hdn)).sub_right hSsc
    · exact Offset.disjoint_below _ (by unfold frameBytes at hdn; omega)
  have hx4 : Spec.RsaPss.expectedSaltLen (stackArg s 0) ((anyV s).setWidth 32) = sLenV s := by
    rw [← expected_eq]
    congr 1
    unfold anyV
    exact BitVec.setWidth_setWidth_of_le _ (by decide)
  have hdg : Spec.Rsa.bytesAt t.mem (s.gpr .x4) T.H.D = Spec.Rsa.bytesAt s.mem (s.gpr .x4) T.H.D := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => ht.mem.bytes (R := ⟨s.gpr .x4, T.H.D⟩) (fun r hr => ?_)
      (by show T.H.D ≤ 2 ^ 64; rw [E.hD]; have := hp.wdg; omega) (List.mem_range.mp hj)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [E.hD]; exact hp.kdg.symm
    · rw [E.hD]; exact hp.dgs
  exact {
    sp := hsp'.trans ht.sp
    rd := hrd'.trans ht.rd
    wr := hwr'.trans ht.wr
    v := fun r hr => (hvs r hr).trans (ht.v r hr)
    fr := ht.fr.frame hf (hA (by decide)) (hA (by decide)) (hA (by decide))
    mem := ht.mem.trans (hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sR s, by simp, hSsc⟩
      · exact ⟨kR K s, by simp, hB⟩)
    x26 := fun hc => by
      rw [hpres .x26 (by decide) (by decide), ht.x26]
      have hb' := ht.res hc
      have e0 : t.mem (scr s) = (pubX s).getD 0 0 := by
        rw [← hb', Sgn.bytesAt_cons _ _ (by omega)]; rfl
      rw [e0]
    x0 := fun hc => by
      rw [hpost, hx4, hdg, ← E.hl, ← ht.res hc, bytesAt_drop, show (s.gpr .x1).toNat - loS s = elS s by omega] }

end VG.Proof.RsaPss.AArch64.Vfy
