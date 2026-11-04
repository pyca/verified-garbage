module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncVerified
public import VerifiedGarbage.Proof.MdHashTable.AArch64
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.HashTable.AArch64

/-!
# RSASSA-PSS signing on AArch64, around the encoding: the call of `encode`

With the parameters in `x24`–`x26` (`AtPar`), `encArgs` writes a zero byte at
`EM` and sets `encode`'s arguments, the tables' addresses on the stack
(`encArgs_ok`, `AtEnc`), which meet its contract for the functions the
tables name (`ESel`, `encPre_of`); after the call of `encode` for the
table's index, `EM` holds `lo` zero bytes and the encoding, or `encode`
returned 0 (`encCall_ok`, `AfterEnc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm wp_subImm wp_movz wp_add wp_strb wp_strx)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov wp_addSp)
open VG.Proof.RsaPss.AArch64 (off off_add ebV Tabs TabsAt held_frame)

/-- The parameters: `emBits = eb`, `emLen = el` and `lo` in `x24`–`x26`. -/
structure AtPar (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame (wrS K s) s.mem t.mem
  fr : Fr s t.mem
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x3
  x24 : t.gpr .x24 = BitVec.ofNat 64 eb
  x25 : t.gpr .x25 = BitVec.ofNat 64 el
  x26 : t.gpr .x26 = BitVec.ofNat 64 lo
  x27 : t.gpr .x27 = s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64

/-- At the call of `encode`, but for the tables: a zero byte at `EM`, `em`
after it. -/
structure AtEnc0 (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop extends AtPar K s eb el lo t where
  x0 : t.gpr .x0 = off (scr s) (oEm + lo)
  x1 : t.gpr .x1 = BitVec.ofNat 64 el
  x2 : t.gpr .x2 = stackArg s 8
  x3 : t.gpr .x3 = stackArg s 10
  x4 : t.gpr .x4 = stackArg s 11
  x5 : t.gpr .x5 = BitVec.ofNat 64 eb
  x6 : t.gpr .x6 = off (scr s) oEnc
  x7 : t.gpr .x7 = stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)
  z : t.mem (off (scr s) oEm) = 0

/-- At the call of `encode`: and the tables' addresses its stack arguments. -/
structure AtEnc (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop extends AtEnc0 K s eb el lo t where
  a0 : stackArg t 0 = stackArg s 14
  a1 : stackArg t 1 = stackArg s 15

/-- `encArgs` without the tables' addresses, and those. -/
abbrev encArgsA : List Instr :=
  [.addImm .x .x0 .x20 oEm, movi .x9 0, .strb .x9 .x0 0, .add .x .x0 .x0 .x26, VG.Impl.MdStream.AArch64.mov .x1 .x25, ld .x2 sDig,
    ld .x3 sSalt, ld .x4 sSaltLen, VG.Impl.MdStream.AArch64.mov .x5 .x24, .addImm .x .x6 .x20 oEnc, ld .x7 sScrLen,
    .subImm .x .x7 .x7 (oEnc / 8)]
abbrev tabArgs : List Instr := [.addSp .x16 0, arg .x9 14, .str .x .x9 .x16 0, arg .x9 15, .str .x .x9 .x16 8]

theorem encArgs_eq : encArgs = encArgsA ++ tabArgs := rfl

/-- Bytes of our working space are writable. -/
theorem scr_wr {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {o n : Nat}
    (h : o + n ≤ 8 * 1024) : InRegions t.wr (off (scr s) o) n := by
  have := hp.hs; have := hp.ws
  rw [hwr]
  exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, Offset.contains_base _ (by omega) (by omega)⟩

/-- A region of our working space is apart from the frame's slots. -/
theorem scr_frA {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) {o n : Nat} (h : o + n ≤ 8 * 1024) :
    (frA s).Disjoint ⟨off (scr s) o, n⟩ ∧ (frB s).Disjoint ⟨off (scr s) o, n⟩ := by
  have := hp.hs
  have hs : Region.Sub ⟨off (scr s) o, n⟩ (sR s) := Offset.sub_base _ (by omega)
  exact ⟨(hp.ks.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))).sub_right hs,
    (hp.ks.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))).sub_right hs⟩

theorem encArgsA_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) {eb el lo : Nat}
    (ha : AtPar K s eb el lo t) : WP isa (.block encArgsA) t (AtEnc0 K s eb el lo) := by
  unfold encArgsA
  have hk2 := hp.k2
  have hin : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  unfold ld
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => ?_
  have x0₂ : u₂.gpr .x0 = off (scr s) oEm := by rw [o₂.get .x0, e₁, ha.x20]
  refine wp_strb (a := off (scr s) oEm) (by decide) (by rw [x0₂, BitVec.add_zero])
    (by rw [o₂.wr, o₁.wr]; exact scr_wr hp ha.wr (by unfold oEm; omega)) fun u₃ m₃ => ?_
  have O₂ : Only [.x0, .x9] t u₂ := (o₁.trans o₂).mono
  have hm₃ : u₃.mem = t.mem.writeW (off (scr s) oEm) (0 : Byte) := by rw [m₃.mem, O₂.mem, e₂]; rfl
  have f₃ : Frame [⟨off (scr s) oEm, 1⟩] t.mem u₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₃ : Fr s u₃.mem := ha.fr.frame f₃
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (scr_frA hp (by unfold oEm; omega)).1)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (scr_frA hp (by unfold oEm; omega)).2)
  have sp₃ : u₃.sp = fb s := by rw [m₃.sp, O₂.sp, ha.sp]
  have rd₃ : u₃.rd = s.rd := by rw [m₃.rd, O₂.rd, ha.rd]
  have wr₃ : u₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₃.wr, O₂.wr, ha.wr]
  refine wp_add fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => ?_
  have O₅ : Only [.x0, .x1] u₃ u₅ := (o₄.trans o₅).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₅.sp, sp₃]) (by rw [O₅.rd, rd₃]) (by rw [O₅.wr, wr₃]) (by decide))
    fun u₆ o₆ e₆ => ?_
  refine wp_ldrSp (by decide) (hin (by rw [o₆.sp, O₅.sp, sp₃]) (by rw [o₆.rd, O₅.rd, rd₃])
    (by rw [o₆.wr, O₅.wr, wr₃]) (by decide)) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x0, .x1, .x2, .x3] u₃ u₇ := (O₅.trans (o₆.trans o₇)).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₇.sp, sp₃]) (by rw [O₇.rd, rd₃]) (by rw [O₇.wr, wr₃]) (by decide))
    fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ => wp_addImm (by unfold oEnc oY; omega) fun u₁₀ o₁₀ e₁₀ => ?_
  have O₁₀ : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6] u₃ u₁₀ := (O₇.trans (o₈.trans (o₉.trans o₁₀))).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₁₀.sp, sp₃]) (by rw [O₁₀.rd, rd₃]) (by rw [O₁₀.wr, wr₃]) (by decide))
    fun u₁₁ o₁₁ e₁₁ => wp_subImm (by unfold oEnc oY; omega) fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have O : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₃ u₁₂ := (O₁₀.trans (o₁₁.trans o₁₂)).mono
  have mem : ∀ {u : State}, Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₃ u → u.mem = u₃.mem := fun o => o.mem
  have g : ∀ r ∈ [Reg.x20, .x23, .x24, .x25, .x26, .x27], u₁₂.gpr r = t.gpr r := fun r hr => by
    rw [O.gpr r (by revert r; decide), m₃.gpr, O₂.gpr r (by revert r; decide)]
  refine {
    sp := by rw [O.sp, sp₃]
    rd := by rw [O.rd, rd₃]
    wr := by rw [O.wr, wr₃]
    v := fun r hr => by rw [O.vcs r hr, m₃.vcs r hr, O₂.vcs r hr, ha.v r hr]
    mem := by
      rw [O.mem]
      exact ha.mem.trans (f₃.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨sR s, by simp, Offset.sub_base _ (by have := hp.hs; unfold oEm; omega)⟩)
    fr := by rw [O.mem]; exact fr₃
    x20 := by rw [g .x20 (by decide), ha.x20]
    x23 := by rw [g .x23 (by decide), ha.x23]
    x24 := by rw [g .x24 (by decide), ha.x24]
    x25 := by rw [g .x25 (by decide), ha.x25]
    x26 := by rw [g .x26 (by decide), ha.x26]
    x27 := by rw [g .x27 (by decide), ha.x27]
    x0 := by
      rw [o₁₂.get .x0, o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, o₈.get .x0, o₇.get .x0, o₆.get .x0, o₅.get .x0, e₄,
        m₃.gpr, x0₂, O₂.get .x26, ha.x26, off_add]
    x1 := by
      rw [o₁₂.get .x1, o₁₁.get .x1, o₁₀.get .x1, o₉.get .x1, o₈.get .x1, o₇.get .x1, o₆.get .x1, e₅, o₄.get .x25,
        m₃.gpr, O₂.get .x25, ha.x25]
    x2 := by
      rw [o₁₂.get .x2, o₁₁.get .x2, o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, e₆, O₅.mem, O₅.sp, sp₃]
      exact fr₃.dig
    x3 := by
      rw [o₁₂.get .x3, o₁₁.get .x3, o₁₀.get .x3, o₉.get .x3, o₈.get .x3, e₇, o₆.mem, O₅.mem, o₆.sp, O₅.sp, sp₃]
      exact fr₃.salt
    x4 := by
      rw [o₁₂.get .x4, o₁₁.get .x4, o₁₀.get .x4, o₉.get .x4, e₈, O₇.mem, O₇.sp, sp₃]
      exact fr₃.sl
    x5 := by
      rw [o₁₂.get .x5, o₁₁.get .x5, o₁₀.get .x5, e₉, o₈.get .x24, O₇.get .x24, m₃.gpr, O₂.get .x24, ha.x24]
    x6 := by
      rw [o₁₂.get .x6, o₁₁.get .x6, e₁₀, o₉.get .x20, o₈.get .x20, O₇.get .x20, m₃.gpr, O₂.get .x20, ha.x20]
    x7 := by
      rw [e₁₂, e₁₁, O₁₀.mem, O₁₀.sp, sp₃]
      rw [fr₃.scr]
    z := by rw [O.mem, hm₃, writeW8_apply, ite_eq_left rfl] }

/-- The `cK ≤ K` bytes below the frame are in the stack the function uses. -/
theorem below_kR {K cK : Nat} (s : State) (hcK : cK ≤ K) :
    Region.Sub ⟨fb s - BitVec.ofNat 64 cK, cK⟩ (kR K s) := fun a h =>
  (Offset.sub_below (fb s) (a := cK) (b := K) (n := cK) (m := K) hcK (by omega_using [hcK]) a h) |>
    fun h' => by
      have e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
      rw [e] at h'
      exact Region.sub_prefix (by unfold stk; omega_using []) a h'

theorem oEnc_toNat {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) :
    (stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 13).toNat - oEnc / 8 := by
  have := hp.hs
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 13).isLt
  unfold oEnc oY at *
  omega

/-- The tables' addresses to the stack arguments of `encode`. -/
theorem tabArgs_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) {eb el lo : Nat}
    (ha : AtEnc0 K s eb el lo t) : WP isa (.block tabArgs) t (AtEnc K s eb el lo) := by
  have hA : ∀ {u : State} (j : Nat), j < 16 → u.sp = fb s → u.rd = s.rd →
      InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 8 * j)) 8 := fun j hj hsp hrd => by
    rw [hsp, hrd, ← stackArgAddr_fb]; exact arg_in hp (Covers.left (Covers.refl _)) hj
  unfold tabArgs arg
  refine wp_addSp (by decide) fun u₁ o₁ e₁ => ?_
  rw [ha.sp, BitVec.add_zero] at e₁
  refine wp_ldrSp (by decide) (hA 14 (by decide) (by rw [o₁.sp, ha.sp]) (by rw [o₁.rd, ha.rd]))
    fun u₂ o₂ e₂ => ?_
  rw [o₁.sp, ha.sp, ← stackArgAddr_fb, o₁.mem, arg_frameW hp ha.mem (by decide)] at e₂
  refine wp_strx (a := fb s + BitVec.ofNat 64 0) (by decide) (by rw [o₂.get .x16, e₁])
    (by rw [o₂.wr, o₁.wr, ha.wr]; exact in_frame s _ (by decide)) fun u₃ m₃ => ?_
  refine wp_ldrSp (by decide) (hA 15 (by decide) (by rw [m₃.sp, o₂.sp, o₁.sp, ha.sp])
    (by rw [m₃.rd, o₂.rd, o₁.rd, ha.rd])) fun u₄ o₄ e₄ => ?_
  have hm₃ : u₃.mem = t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 14) := by
    rw [m₃.mem, o₂.mem, o₁.mem, e₂]
  have f₃ : Frame (wrS K s) s.mem u₃.mem := by
    rw [hm₃]
    exact ha.mem.writeW (r := ⟨fb s, frameBytes⟩) (by simp [wrS]) _ (Offset.contains_base _ (by decide) (by decide))
  rw [m₃.sp, o₂.sp, o₁.sp, ha.sp, ← stackArgAddr_fb, arg_frameW hp f₃ (by decide)] at e₄
  refine wp_strx (a := fb s + BitVec.ofNat 64 8) (by decide) (by rw [o₄.get .x16, m₃.gpr, o₂.get .x16, e₁])
    (by rw [o₄.wr, m₃.wr, o₂.wr, o₁.wr, ha.wr]; exact in_frame s _ (by decide)) fun u₅ m₅ => wp_nil ?_
  have hm₅ : u₅.mem = (t.mem.writeW (fb s + BitVec.ofNat 64 0) (stackArg s 14)).writeW (fb s + BitVec.ofNat 64 8)
      (stackArg s 15) := by rw [m₅.mem, o₄.mem, hm₃, e₄]
  have hf : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] t.mem u₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by decide) (by decide) (by decide))
  have K₅ : Keep [.x16, .x9] t u₅ := (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans m₅.keep)))).mono
  have g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x20, .x23, .x24, .x25, .x26, .x27],
      u₅.gpr r = t.gpr r := fun r hr => K₅.get r (by revert r; decide)
  have sp₅ : u₅.sp = fb s := K₅.sp.trans ha.sp
  have hS : Region.Sub ⟨off (scr s) oEm, 1⟩ (sR s) := Offset.sub_base _ (by have := hp.hs; unfold oEm; omega)
  have hd16 : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)], (frA s).Disjoint r ∧ (frB s).Disjoint r :=
      fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (by decide) (by decide) (by decide), Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  exact {
    sp := sp₅
    rd := K₅.rd.trans ha.rd
    wr := K₅.wr.trans ha.wr
    v := fun r hr => (K₅.vcs r hr).trans (ha.v r hr)
    mem := ha.mem.trans (hf.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨⟨fb s, frameBytes⟩, by simp [wrS], by rw [BitVec.add_zero]; exact Region.sub_prefix (by decide)⟩)
    fr := ha.fr.frame hf (fun r hr => (hd16 r hr).1) (fun r hr => (hd16 r hr).2)
    x20 := (g _ (by simp)).trans ha.x20
    x23 := (g _ (by simp)).trans ha.x23
    x24 := (g _ (by simp)).trans ha.x24
    x25 := (g _ (by simp)).trans ha.x25
    x26 := (g _ (by simp)).trans ha.x26
    x27 := (g _ (by simp)).trans ha.x27
    x0 := (g _ (by simp)).trans ha.x0
    x1 := (g _ (by simp)).trans ha.x1
    x2 := (g _ (by simp)).trans ha.x2
    x3 := (g _ (by simp)).trans ha.x3
    x4 := (g _ (by simp)).trans ha.x4
    x5 := (g _ (by simp)).trans ha.x5
    x6 := (g _ (by simp)).trans ha.x6
    x7 := (g _ (by simp)).trans ha.x7
    z := by
      rw [hf _ fun r hr hc => ?_]
      · exact ha.z
      rw [List.mem_singleton.mp hr] at hc
      exact (hp.ks.sub_left (frame_sub K s (d := 0) (n := 16) (by decide))).sub_right hS _ hc
        (Region.contains_self _ _)
    a0 := by
      show u₅.mem.readW (u₅.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
      rw [hm₅, sp₅, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_self64]
    a1 := by
      show u₅.mem.readW (u₅.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
      rw [hm₅, sp₅, Mem.readW_writeW_self64] }

theorem encArgs_ok {tsH tsG : List FnTable} {K : Nat} {s t : State} (hp : PreS tsH tsG K s) {eb el lo : Nat}
    (ha : AtPar K s eb el lo t) : WP isa (.block encArgs) t (AtEnc K s eb el lo) := by
  rw [encArgs_eq, WP.block_append_iff]
  exact WP.mono (encArgsA_ok hp ha) fun u hu => tabArgs_ok hp hu

/-- What the tables at the stack arguments 14 and 15 of `s` give the call of
`encode` for the index `i` of the table of `MdHash`: the tables of the
precondition that they are, the functions `T` of both tables, the hash
functions `Hs` and `Gs` they name, and that `encode` for the index `i`
computes the encoding with them. -/
structure ESel (f : MdFns) (g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns) (tsH tsG : List FnTable) (s : State) (i : Nat)
    (T : Tabs) (Hs Gs : Spec.Mgf1.Hash) : Prop where
  mem : i ∈ idxs
  idx : s.mem.readW (stackArg s 14 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 i
  eH : T.tsH = tsH
  eG : T.tsG = tsG
  selH : ∃ TH ∈ tsH, (FnTable.words isa s TH).length = 11 ∧
    Abi.tableHeld 64 s.mem (stackArg s 14) (FnTable.words isa s TH)
  selG : ∃ TG ∈ tsG, (FnTable.words isa s TG).length = 5 ∧
    Abi.tableHeld 64 s.mem (stackArg s 15) (FnTable.words isa s TG)
  tabs : TabsAt T.H T.dn T.f T.G T.g (stackArg s 14) (stackArg s 15) s
  hH : Spec.MdHashTable.hashAt 64 s.mem (stackArg s 14) = some Hs
  hG : Spec.HashTable.hashAt 64 s.mem (stackArg s 15) = some Gs
  hD : T.H.D = (stackArg s 9).toNat
  ok : ∀ s', (Enc.encK T Hs Gs).pre s' → ∃ t s'', Exec isa (encode f (ofIdx i) g) s' t s'' ∧
    abiPreserved s' s'' ∧ (Enc.encK T Hs Gs).post s' s''
  depth : (encode f (ofIdx i) g).aarch64Depth ≤ 39

/-- The regions a call of `encode` reads and writes. -/
abbrev encRdT (D : Nat) (t : State) : List Region :=
  [⟨t.gpr .x2, D⟩, ⟨t.gpr .x3, (t.gpr .x4).toNat⟩, Sig.tableRegion 64 (stackArg t 0) 11,
    Sig.tableRegion 64 (stackArg t 1) 5, ⟨stackArgAddr t 0, 16⟩]
abbrev encWrT (t : State) : List Region := [⟨t.gpr .x0, (t.gpr .x1).toNat⟩, ⟨t.gpr .x6, (t.gpr .x7).toNat * 8⟩]

/-- The tables, after writes only to our frame, our working space and the stack below. -/
theorem tabs_wrS {tsH tsG : List FnTable} {K : Nat} {s : State} (hp : PreS tsH tsG K s) :
    (∀ r ∈ wrS K s, Region.Disjoint ⟨stackArg s 14, 88⟩ r) ∧ (∀ r ∈ wrS K s, Region.Disjoint ⟨stackArg s 15, 40⟩ r) :=
  ⟨fun r hr => wrS_disj hp.ktH hp.stH.symm r hr, fun r hr => wrS_disj hp.ktG hp.stG.symm r hr⟩

/-- The call's arguments meet `encode`'s contract. -/
theorem encPre_of {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} {K : Nat}
    {s t : State} (hp : PreS tsH tsG K s) (h624 : 624 ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) {eb el lo : Nat}
    (ha : AtEnc K s eb el lo t) (hsy : t.syms = s.syms) (hlo : lo + el ≤ (s.gpr .x3).toNat)
    (hel : el = Spec.RsaPss.emLength eb) (hb1 : 1 ≤ eb) (hb2 : eb ≤ Proof.RsaPss.maxEmBits) :
    (Enc.encK T Hs Gs).pre (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hsp1 := hp.sp1
  have hws : (scr s).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  have hsc := oEnc_toNat hp
  have hK := below_kR (K := K) (cK := stk 288) s (by unfold stk frameBytes; omega)
  have hSem : Region.Sub ⟨off (scr s) (oEm + lo), el⟩ (sR s) :=
    Offset.sub_base _ (by unfold oEm; omega)
  have hSsc : Region.Sub ⟨off (scr s) oEnc, (stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold oEnc oY at *; omega)
  have hA : Region.Sub ⟨fb s + BitVec.ofNat 64 (8 * 0), 16⟩ (kR K s) := frame_sub K s (by decide)
  have hwem : (off (scr s) (oEm + lo)).toNat + el ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm at *; omega
  have hwsc : (off (scr s) oEnc).toNat + (stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; unfold oEnc oY at *; omega
  have he : (BitVec.ofNat 64 el).toNat = el := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show el < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show eb < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hD := E.hD
  obtain ⟨dH, dG⟩ := tabs_wrS hp
  have hsc0 : (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)).syms = s.syms := hsy
  have hm0 : (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)).mem = t.mem := rfl
  have hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7],
      (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)).gpr r = t.gpr r := by
    intro r hr; simp only [State.withRegions_gpr, State.callEntry]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have a0 : stackArg (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)) 0 = stackArg s 14 := ha.a0
  have a1 : stackArg (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)) 1 = stackArg s 15 := ha.a1
  have sp0 : (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)).sp = fb s := ha.sp
  have aA : stackArgAddr (t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)) 0 = fb s + BitVec.ofNat 64 (8 * 0) := by
    rw [stackArgAddr, sp0]
  have hsy' : ∀ x : State, x.syms = s.syms → ∀ T' : FnTable, FnTable.words isa x T' = FnTable.words isa s T' :=
    fun x hx T' => VG.Proof.HashTable.AArch64.words_congr hx T'
  refine ⟨⟨?sp1, ?sp2, ?tabH, ?tabG, ?hsy, rfl, rfl, ?ed, ?esa, ?es, ?etH, ?etG, ?eA, ?ds, ?sas, ?stH, ?stG, ?sA,
    ?ke, ?kd, ?ksa, ?ks, ?ktH, ?ktG, ?kA, ?we, ?wd, ?wsa, ?ws, ?wtH, ?wtG, ?b1, ?b2, ?hel, ?hs⟩, ?tabs⟩
  all_goals try simp only [Enc.emR, Enc.dgR, Enc.saR, Enc.sR, Enc.tHR, Enc.tGR, Enc.aR, Sgn.kR,
    hg .x0 (by simp), hg .x1 (by simp), hg .x2 (by simp), hg .x3 (by simp), hg .x4 (by simp), hg .x5 (by simp),
    hg .x6 (by simp), hg .x7 (by simp), a0, a1, aA, sp0, ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, he, hb]
  case sp1 => unfold Enc.encStack stk frameBytes at *; omega
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
  case ed => rw [hD]; exact hp.dgs.symm.sub_left hSem
  case esa => exact hp.sls.symm.sub_left hSem
  case es =>
    exact Offset.disjoint _ (Or.inl (by unfold oEm oEnc oY; omega)) (by unfold oEm; omega)
      (by rw [hsc]; unfold oEnc oY at *; omega)
  case etH => exact hp.stH.sub_left hSem
  case etG => exact hp.stG.sub_left hSem
  case eA => exact ((hp.ks.sub_left hA).sub_right hSem).symm
  case ds => rw [hD]; exact hp.dgs.sub_right hSsc
  case sas => exact hp.sls.sub_right hSsc
  case stH => exact hp.stH.sub_left hSsc
  case stG => exact hp.stG.sub_left hSsc
  case sA => exact ((hp.ks.sub_left hA).sub_right hSsc).symm
  case ke => exact (hp.ks.sub_left hK).sub_right hSem
  case kd => rw [hD]; exact hp.kdg.sub_left hK
  case ksa => exact hp.ksl.sub_left hK
  case ks => exact (hp.ks.sub_left hK).sub_right hSsc
  case ktH => exact hp.ktH.sub_left hK
  case ktG => exact hp.ktG.sub_left hK
  case kA =>
    rw [show fb s + BitVec.ofNat 64 (8 * 0) = fb s from BitVec.add_zero _]
    exact (Offset.base_disjoint_below (fb s) (n := stk 288) (k := 16) (by unfold stk frameBytes; omega)).symm
  case we => exact hwem
  case wd => rw [hD]; exact hp.wdg
  case wsa => exact hp.wsl
  case ws => exact hwsc
  case wtH => exact hp.wtH
  case wtG => exact hp.wtG
  case b1 => exact hb1
  case b2 => exact hb2
  case hel => exact hel
  case hs => rw [hsc]; unfold Proof.RsaPss.encScratch oEnc oY; omega
  case tabs =>
    show TabsAt T.H T.dn T.f T.G T.g (stackArg _ 0) (stackArg _ 1) _
    rw [a0, a1]
    exact E.tabs.frame (t := t.callEntry.withRegions (encRdT T.H.D t) (encWrT t)) ha.mem dH dG hsc0

variable (Hs Gs : Spec.Mgf1.Hash) in
/-- After the call of `encode`: its result, and `EM` holding `lo` zero bytes
and the encoding if it fits. -/
structure AfterEnc (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Fr s t.mem
  mem : Frame (wrS K s) s.mem t.mem
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x3
  z : lo = 1 → t.mem (off (scr s) oEm) = 0
  res : match Spec.RsaPss.encode Hs Gs (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 10) (stackArg s 11).toNat) eb with
    | some e => (t.gpr .x0).setWidth 32 = (1 : BitVec 32) ∧
        Spec.Rsa.bytesAt t.mem (off (scr s) (oEm + lo)) el = e
    | none => (t.gpr .x0).setWidth 32 = (0 : BitVec 32)

theorem encCall_ok {f : MdFns} {g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {tsH tsG : List FnTable} {K : Nat}
    {s t : State} (hp : PreS tsH tsG K s) (h624 : 624 ≤ K) {i : Nat} {T : Tabs} {Hs Gs : Spec.Mgf1.Hash}
    (E : ESel f g tsH tsG s i T Hs Gs) {eb el lo : Nat}
    (ha : AtEnc K s eb el lo t) (hsy : t.syms = s.syms) (hlo : lo + el ≤ (s.gpr .x3).toNat)
    (hel : el = Spec.RsaPss.emLength eb) (hb1 : 1 ≤ eb) (hb2 : eb ≤ Proof.RsaPss.maxEmBits) :
    WP isa (.call (encName i) (encode f (ofIdx i) g)) t (AfterEnc Hs Gs K s eb el lo) := by
  have hk2 := hp.k2
  have hhs := hp.hs
  have hws : (scr s).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hd := E.depth
  have hsc := oEnc_toNat hp
  have he : (BitVec.ofNat 64 el).toNat = el := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show el < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show eb < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hSem : Region.Sub ⟨off (scr s) (oEm + lo), el⟩ (sR s) := Offset.sub_base _ (by unfold oEm; omega)
  have hSsc : Region.Sub ⟨off (scr s) oEnc, (stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold oEnc oY at *; omega)
  have hcr : Covers (encRdT T.H.D t) (t.rd ++ t.wr) := by
    simp only [encRdT, ha.x2, ha.x3, ha.x4, ha.a0, ha.a1, E.hD]
    rw [ha.rd, ha.wr]
    have hm : ∀ r ∈ [dgR s, slR s, tHR s, tGR s], Covers [r] (s.rd ++ (⟨fb s, frameBytes⟩ :: s.wr)) :=
      fun r hr => Covers.left (Covers.trans (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h <;> simp [h]) hp.hrd)
    exact Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp)) (Covers.cons (hm _ (by simp))
      (Covers.cons (hm _ (by simp)) (Covers.right (Covers.one (by
        rw [stackArgAddr, ha.sp]; exact in_frame s s.wr (d := 8 * 0) (n := 16) (by decide)))))))
  have hcw : Covers (encWrT t) t.wr := by
    simp only [encWrT, ha.x0, ha.x1, ha.x6, ha.x7, he]
    rw [ha.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, oEm + lo, rfl,
        by show oEm + lo + el ≤ (stackArg s 13).toNat * 8; unfold oEm; omega⟩
    · exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, oEnc, rfl,
        by show oEnc + (stackArg s 13 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8 ≤ (stackArg s 13).toNat * 8
           rw [hsc]; unfold oEnc oY at *; omega⟩
  refine WP.callFV (k := Enc.encK T Hs Gs) E.ok (encPre_of hp h624 E ha hsy hlo hel hb1 hb2)
    (Covers.append_left hcr (Covers.right hcw)) hcw ?_ (by omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  have hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5], t.callEntry.gpr r = t.gpr r := by
    intro r hr; simp only [State.callEntry]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  simp only [Enc.encK, Enc.OutOk, Enc.encOut, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    hg .x0 (by simp), hg .x1 (by simp), hg .x2 (by simp), hg .x3 (by simp), hg .x4 (by simp), hg .x5 (by simp),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, he, hb, E.hD] at hpost
  simp only [encWrT] at hf
  rw [ha.x0, ha.x1, ha.x6, ha.x7, ha.sp, he] at hf
  have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega
  rw [bytes_wrS ha.mem hp.kdg hp.dgs (hl hp.wdg), bytes_wrS ha.mem hp.ksl hp.sls (hl hp.wsl)] at hpost
  have hB : Region.Sub (below (fb s) (16 * (encode f (ofIdx i) g).aarch64Depth)) (below (fb s) K) :=
    Offset.sub_below _ (by omega) (by omega)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    fr := ha.fr.below (n := 16 * (encode f (ofIdx i) g).aarch64Depth) (by omega) hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (scr_frA hp (by unfold oEm; omega)).1
        · exact (hp.ks.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))).sub_right hSsc)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (scr_frA hp (by unfold oEm; omega)).2
        · exact (hp.ks.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))).sub_right hSsc)
    mem := ha.mem.trans (hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sR s, by simp, hSem⟩
      · exact ⟨sR s, by simp, hSsc⟩
      · exact ⟨below (fb s) K, by simp, hB⟩)
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    x23 := (hpres .x23 (by decide) (by decide)).trans ha.x23
    z := fun h1 => by
      subst h1
      rw [hf _ fun r hr hc => ?_]
      · exact ha.z
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hc0 : (⟨off (scr s) oEm, 1⟩ : Region).Contains (off (scr s) oEm) 1 := Region.contains_self _ _
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (Or.inl (by omega)) (by unfold oEm; omega) (by unfold oEm; omega) _ hc0 hc
      · exact Offset.disjoint _ (Or.inl (by unfold oEm oEnc oY; omega)) (by unfold oEm; omega)
          (by rw [hsc]; unfold oEnc oY at *; omega) _ hc0 hc
      · exact (hp.ks.sub_left (below_kR (cK := 16 * (encode f (ofIdx i) g).aarch64Depth) s (by omega))).sub_right
          (Offset.sub_base _ (by unfold oEm; omega) : Region.Sub ⟨off (scr s) oEm, 1⟩ (sR s)) _ hc hc0
    res := hpost }

end VG.Proof.RsaPss.AArch64.Sgn
