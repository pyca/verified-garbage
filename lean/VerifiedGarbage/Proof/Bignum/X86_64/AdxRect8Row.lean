module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `Bignum.X86_64.AdxRect8Setup`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxRect8Frame`, which the modules that import this one used -/

section

/-! ## AdxRect8Counter -/

@[expose] public section

section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextColumn_ok {s : State} {B : Addr} {Z w j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j+8 < 2^64) (hw : w < 2^64)
    (hidx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block AdxRect8.nextColumn) s fun t =>
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8)) ∧
      t.zf = some (decide (j+8=w)) ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have hiZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega_using [hZ, this]
  have hwZ : 8*sW+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sW < 32 by decide); omega_using [hZ, this]
  unfold AdxRect8.nextColumn
  rw [show ([.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 13)) .rax, .alu .cmp .rax (.mem (hdr sW))] : List Instr) =
      [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8), .store (hdr (sFn 13)) .rax] ++
      [.alu .cmp .rax (.mem (hdr sW))] from rfl, WP.block_append_iff]
  have first : WP isa (.block [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
      .store (hdr (sFn 13)) .rax]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8)) ∧ Keep [.rax] s t := by
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (j+8) ∧
      t.mem = s.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j+8))) ?_ rfl)
      fun t ⟨⟨a,b⟩,k⟩ => ⟨a,b,k⟩
    xrun [State.ea,hdr,hd,hdrOff,hs.ld hiZ,hs.st hiZ,hidx,
      show (8 : BitVec 32).signExtend 64 = 8 from rfl,BitVec.ofNat_add]
    exact ⟨rfl,rfl⟩
  refine WP.mono first fun a ⟨ra,ma,ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have wa : word a.mem B (8*sW) = BitVec.ofNat 64 w := by
    rw [ma,(writeW_outside s.mem B (BitVec.ofNat 64 (j+8)) (by omega_using [hn, hiZ] : 8*sFn 13+8 ≤ 2^64)).word
      (by decide : 8*sW+8 ≤ 8*sFn 13 ∨ 8*sFn 13+8 ≤ 8*sW) (by omega_using [hn, hwZ]),hh.hw]
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = a.mem ∧ t.zf = some (decide (j+8=w))) ?_ rfl)
    fun t ⟨⟨mt,zt⟩,kt⟩ => ⟨mt.trans ma,zt,(ka.trans kt).mono (by simp)⟩
  xrun [State.ea,hdr,(ka.gpr (by decide)).trans hd,hdrOff,sa.ld hwZ,wa,ra,ofNat_sub_beq hj hw]

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Frame -/
section

namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The tile's temporary header words do not overlap the Montgomery header. -/
theorem frame_hdr {m m' : Mem} {B : Addr} {w e n : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Hdr m' B w mi := by
  have low (k : Nat) (hk : k < 16) : word m' B (8*k) = word m B (8*k) := by
    apply hf.word_eq
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        unfold carryOffset sFn hdrBytes at * <;> omega_arith
    · omega_using [hk]
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun k hk => (low (sArr k) (by unfold sArr; omega_using [hk])).trans (hh.harr k hk)⟩

/-- Nor the slots of the operands' bases. -/
theorem frame_ops {m m' : Mem} {B : Addr} {w e n : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (he : hdrBytes ≤ e)
    (hf : Frm B [(e,n),(carryOffset,8),(8*sFn 13,8)] m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> unfold carryOffset sFn hdrBytes at * <;> omega_arith

/-- Two adjacent scratch arrays contain every rectangular tile. -/
theorem tile_ranges {w i j a : Nat} (hi : i+8 ≤ w) (hj : j+8 ≤ w)
    (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) :
    slot w a+8*i+64 ≤ slot w 8 ∧
    slot w aAcc+16+8*(i+j)+128 ≤ slot w 8 ∧
    (slot w a+8*i+64 ≤ slot w aAcc+16+8*(i+j) ∨
      slot w aAcc+16+8*(i+j)+128 ≤ slot w a+8*i) := by
  have sa := slot_le (w := w) ha
  have st := slot_le (w := w) (show aTmp < 8 by decide)
  have s1 := slot_sep (w := w) ha1
  have s2 := slot_sep (w := w) ha2
  unfold slot aAcc aTmp at *
  omega_using [hi, hj, sa, s1, s2]

end VG.Proof.Bignum.X86_64.AdxRect8

end

end

end

/-! ### `Bignum.X86_64.AdxDualAddInput`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxDualAdd
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols number cols_keep number_words)
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax = 0 ∧ t.cf = some false ∧ t.of = some false ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem addInput_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxDualAdd.addInput) s fun t =>
      cols t + 2^512 * (t.gpr .rax).toNat =
        cols s + wv s.mem B e 8 + (s.gpr .rdx).toNat ∧
      (t.gpr .rax).toNat ≤ 2 ∧ t.cf = some false ∧ t.of = some false ∧
      Keeps [.rax,.rdx,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  unfold AdxDualAdd.addInput
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRax_ok s) fun a ⟨za,hca,hoa,ka⟩ => ?_
  rw [WP.block_append_iff]
  have srcA : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs a t →
      readSrc t (.mem (at_ .rsi (8*k))) = some (word s.mem B (e+8*k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxDualAdd.regs, at_]) (by intro r h; nomatch h),
      ka.readMem (by simp [at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (AdxRotate8.ea_at hp (8*k)) (by omega_using [he, hk])
  have srcB : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs a t →
      readSrc t (.reg (if k = 0 then .rdx else .rax)) =
        some (if k = 0 then s.gpr .rdx else 0) := by
    intro k _ t kt
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, readSrc,
        kt.gpr (r := .rdx) (by decide), ka.gpr (r := .rdx) (by decide)]
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rax) (by decide), za]
  refine WP.mono (chain_ok a _ _ _ _ hca hoa srcA srcB
    (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h))
    fun b ⟨cb,ob,hcb,hob,eb,kb⟩ => ?_
  refine WP.mono (close_ok b hcb hob ((kb.gpr (by decide)).trans za))
    fun t ⟨et,hct,hot,kt⟩ => ?_
  rw [number_words, cols_keep ka.keep (by decide)] at eb
  simp only [number, Nat.reduceEqDiff, ↓reduceIte,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Bool.toNat_false] at eb
  refine ⟨?_,?_,hct,hot,(ka.trans (kb.trans kt)).mono (by simp [AdxDualAdd.regs])⟩
  · rw [cols_keep kt.keep (by decide), et]
    exact eb
  · rw [et]; have bc := Bool.toNat_le cb; have bo := Bool.toNat_le ob; omega_using [bc, bo]

end VG.Proof.Bignum.X86_64.AdxDualAdd

end

end


/-! ## AdxRect8Product -/

@[expose] public section

section

/-! Register products with either ordering of the disjoint input and output buffers. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem productN_disjoint_ok {s : State} {B : Addr} {Z eU eO eN n : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (huZ : eU + 8 * n ≤ Z)
    (hoZ : eO + 8 * n ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 8 * n ≤ eO ∨ eO + 8 * n ≤ eU)
    (hsepN : eN + 64 ≤ eO ∨ eO + 8 * n ≤ eN) :
    WP isa (AdxRotate8.productN n) s fun t =>
      wv t.mem B eO n + 2 ^ (64 * n) * cols t =
        cols s + wv s.mem B eU n * wv s.mem B eN 8 ∧
      Outside B eO (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add],
      Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.productN
    refine WP.seq (WP.mono (ih (by omega_using [huZ]) (by omega_using [hoZ]) (by omega_using [hsepU]) (by omega_using [hsepN])) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    refine WP.mono (productStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho)
      (by omega_using [huZ]) (by omega_using [hoZ]) hnZ) fun t ⟨vt, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega_using [hsepN]) (by omega_using [hnZ, hna])
    have mu : word a.mem B (eU + 8 * n) = word s.mem B (eU + 8 * n) := oa.word (by omega_using [hsepU]) (by omega_using [huZ, hna])
    have lo : wv t.mem B eO n = wv a.mem B eO n := ot.wv (by omega_using []) (by omega_using [hoZ, hna])
    refine ⟨?_, (oa.mono (o' := eO) (n' := 8 * (n + 1)) (by omega_using []) (by omega_using [])).trans
      (ot.mono (o' := eO) (n' := 8 * (n + 1)) (by omega_using []) (by omega_using [])), (ka.trans kt).mono (by decide)⟩
    rw [mn, mu] at vt
    rw [wv, wv, lo, pow64_succ]
    grind
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRect8Tile -/
section

/-! A rectangular tile adds an 8-by-8 product, keeping its upper words in the columns. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

theorem upper_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hp : s.gpr .rsi = off B e)
    (he : carryOffset + 8 ≤ Z) :
    WP isa (.block AdxRect8.upper) s fun t =>
      t.gpr .rdx = word s.mem B carryOffset ∧ t.gpr .rsi = off B (e+64) ∧
      t.mem = s.mem ∧ Keep [.rdx,.rsi] s t := by
  refine WP.mono (WP.keep [.rdx,.rsi] (Q := fun t =>
    t.gpr .rdx = word s.mem B carryOffset ∧ t.gpr .rsi = off B (e+64) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a,b,c⟩,k⟩ => ⟨a,b,c,k⟩
  unfold AdxRect8.upper
  have load := hs.ld he
  change InRegions (s.rd ++ s.wr) (off B (8*sFn 14)) 8 at load
  xrun [State.ea,hdr,hd,hdrOff,hp,load,
    show (64 : BitVec 32).signExtend 64 = 64 from rfl]
  simp only [carryOffset,off,BitVec.ofNat_add,BitVec.add_assoc]
  exact ⟨True.intro,rfl⟩

/-- The end of `streamTile`: the carry into its header slot and `rbp` to the
next column block. -/
theorem streamEnd_ok {s : State} {B : Addr} {Z eB : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hb : s.gpr .rbp = off B eB)
    (he : carryOffset + 8 ≤ Z) :
    WP isa (.block [.store (hdr (sFn 14)) .rax, .alu .add .rbp (.imm 64)]) s fun t =>
      word t.mem B carryOffset = s.gpr .rax ∧ Outside B carryOffset 8 s.mem t.mem ∧
      t.gpr .rbp = off B (eB+64) ∧ Keep [.rbp] s t := by
  rw [show ([.store (hdr (sFn 14)) .rax, .alu .add .rbp (.imm 64)] : List Instr) =
    [.store (hdr (sFn 14)) .rax] ++ [.alu .add .rbp (.imm 64)] from rfl, WP.block_append_iff]
  have address : s.ea (hdr (sFn 14)) = off B carryOffset := by
    simp only [State.ea,hdr,hd,hdrOff,carryOffset]
  refine WP.mono (storeMem_ok hs address he) fun a ⟨wa,oa,ka⟩ => ?_
  have pa : a.gpr .rbp = off B eB := (ka.gpr (by simp)).trans hb
  refine WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = off B (eB+64) ∧ t.mem = a.mem) ?_ rfl)
    fun t ⟨⟨pt,mt⟩,kt⟩ => ?_
  · xrun [pa, show (64 : BitVec 32).signExtend 64 = 64 from rfl]
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  · rw [mt]
    exact ⟨wa,oa,pt,(ka.trans kt).mono (by simp)⟩

/-- A tile whose upper words stay in the columns: the eight products, with
the columns as the tile's low words, into eight output words, and the next
eight output words and the carry added to the columns. -/
theorem streamTile_ok {s : State} {B : Addr} {Z eA eB eO : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (ha : s.gpr .rcx = off B eA)
    (hb : s.gpr .rbp = off B eB) (ho : s.gpr .rsi = off B eO)
    (hA : eA + 64 ≤ Z) (hB : eB + 64 ≤ Z) (hO : eO + 128 ≤ Z)
    (sepA : eA + 64 ≤ eO ∨ eO + 128 ≤ eA)
    (sepB : eB + 64 ≤ eO ∨ eO + 128 ≤ eB)
    (sepC : carryOffset + 8 ≤ eO) :
    WP isa AdxRect8.streamTile s fun t =>
      wv t.mem B eO 8 + 2^512 * cols t + 2^512 * 2^512 * (word t.mem B carryOffset).toNat =
        cols s + 2^512 * wv s.mem B (eO+64) 8 + wv s.mem B eA 8 * wv s.mem B eB 8 +
          2^512 * (word s.mem B carryOffset).toNat ∧
      (word t.mem B carryOffset).toNat ≤ 2 ∧
      ((word s.mem B carryOffset).toNat ≤ 1 → (word t.mem B carryOffset).toNat ≤ 1) ∧
      Frm B [(eO,64),(carryOffset,8)] s.mem t.mem ∧ t.gpr .rsi = off B (eO+64) ∧
      t.gpr .rbp = off B (eB+64) ∧
      Keep [.rdx,.rax,.rbx,.rsi,.rbp,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15] s t := by
  have nowrap := hs.nowrap
  unfold AdxRect8.streamTile
  refine WP.seq (WP.mono (productN_disjoint_ok (n := 8) hs ha hb ho (by omega_using [hA]) (by omega_using [hO]) hB
    (by omega_using [sepA]) (by omega_using [sepB])) fun a ⟨ea,oa,ka⟩ => ?_)
  refine WP.seq (WP.mono (upper_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hd)
    ((ka.gpr (by decide)).trans ho) (by omega_using [hO, sepC])) fun b ⟨db,pb,mb,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.seq (WP.mono (AdxDualAdd.addInput_ok (hs.congr kab.2.2) pb (by omega_using [hO]))
    fun c ⟨ec,bc,_,_,kc⟩ => ?_)
  have kabc := kab.trans kc.keep
  refine WP.mono (streamEnd_ok (hs.congr kabc.2.2) ((kabc.gpr (by decide)).trans hd)
    ((kabc.gpr (by decide)).trans hb) (by omega_using [hO, sepC])) fun t ⟨wt,ot,pt,kt⟩ => ?_
  have carryA : word a.mem B carryOffset = word s.mem B carryOffset :=
    oa.word (by omega_using [sepC]) (by omega_using [hO, sepC, nowrap])
  have upperA : wv a.mem B (eO+64) 8 = wv s.mem B (eO+64) 8 :=
    oa.wv (by omega_using []) (by omega_using [hO, nowrap])
  have lowT : wv t.mem B eO 8 = wv a.mem B eO 8 := by
    rw [ot.wv (by omega_using [sepC]) (by omega_using [hO, nowrap]),kc.2.1,mb]
  have colsT : cols t = cols c := cols_keep kt (by decide)
  rw [cols_keep kb (by decide),mb,db,carryA,upperA] at ec
  simp only [Nat.reduceMul] at ea
  refine ⟨?_,?_,?_,?_,(kt.gpr (by simp)).trans ((kc.1 .rsi (by decide)).trans pb),pt,
    (kabc.trans kt).mono (by decide)⟩
  · rw [wt,lowT,colsT]
    omega_using [ea,ec]
  · rw [wt]; exact bc
  · intro cin
    rw [wt]
    have ca := cols_lt a
    have cc := cols_lt c
    have hi := wv_lt s.mem B (eO+64) 8
    simp only [Nat.reduceMul] at hi
    omega_using [ec,ca,cc,hi,cin]
  · have ab : Outside B eO 64 s.mem c.mem := by
      rw [kc.2.1,mb]; exact oa
    exact (Frm.of_outside ab (by simp)).trans (Frm.of_outside ot (by simp))

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Setup -/
section

/-! Tile addresses depend only on the public word indices and array layout. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem shift3 (n : Nat) : (BitVec.ofNat 64 n) <<< (3 : Nat) = BitVec.ofNat 64 (8*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8*n)
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem setup_ok {s : State} {B : Addr} {Z w i j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb a b : Nat}
    (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hi : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hj : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j) :
    WP isa (.block (AdxRect8.setup ca cb)) s fun t =>
      t.gpr .rcx = off B (slot w a+8*i) ∧
      t.gpr .rbp = off B (slot w b+8*j) ∧
      t.gpr .rsi = off B (slot w aAcc+16+8*(i+j)) ∧
      t.mem = s.mem ∧ Keep [.rax,.rdx,.rcx,.rbp,.rsi] s t := by
  have hl : ∀ k < 32, InRegions (s.rd ++ s.wr) (off B (8*k)) 8 := fun k hk =>
    hs.ld (by have := hdr_lt_slot w 8 hk; omega_using [hZ, this])
  refine WP.mono (WP.keep [.rax,.rdx,.rcx,.rbp,.rsi] (Q := fun t =>
    t.gpr .rcx = off B (slot w a+8*i) ∧
    t.gpr .rbp = off B (slot w b+8*j) ∧
    t.gpr .rsi = off B (slot w aAcc+16+8*(i+j)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc,hp,ho,hm⟩,k⟩ => ⟨hc,hp,ho,hm,k⟩
  unfold AdxRect8.setup
  xrun [State.ea,hdr,hd,hdrOff,hl (sFn 12) (by decide),hl (sFn 13) (by decide),
    hl (sArr ca) (by have := hv.lt pa; unfold sArr; omega_using [this]),hl (sArr cb) (by have := hv.lt pb; unfold sArr; omega_using [this]),
    hl (sArr aAcc) (by decide),hi,hj,show word s.mem B (8*sArr ca) = _ from hv.at pa,
    show word s.mem B (8*sArr cb) = _ from hv.at pb,hh.harr aAcc (by decide),
    shift3,show (16 : BitVec 32).signExtend 64 = 16 from rfl]
  simp only [off,BitVec.ofNat_add,Nat.mul_add,BitVec.add_assoc, true_and]
  have commute (x y z : BitVec 64) : x+(y+z)=z+(x+y) := by
    rw [← BitVec.add_assoc,BitVec.add_comm]
  exact congrArg (fun x : BitVec 64 => B+(BitVec.ofNat 64 (slot w aAcc)+x))
    (commute _ _ _)

end VG.Proof.Bignum.X86_64.AdxRect8

end

end

end

/-! ### `Bignum.Rectangular`, which this module and modules that import it used -/

section

/-! Positional arithmetic for rows of rectangular multiplication tiles. -/

@[expose] public section

namespace VG.Proof.Bignum.Rectangular

theorem extend_carry {L P C T I O R D A : Nat}
    (prev : L+P*C=T+I) (step : O+R*D=A+C) :
    L+P*O+(P*R)*D=T+P*A+I := by
  grind

end VG.Proof.Bignum.Rectangular

end

end

@[expose] public section

/-! ## AdxRect8RowInv -/
section

/-! The invariant keeps the full product plus its pending row carry exact. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def rawBase (w : Nat) := slot w aAcc+16

def rowRanges (w : Nat) : List (Nat × Nat) :=
  [(rawBase w,16*w),(carryOffset,8),(8*sFn 13,8)]

/-- After the row's `k` column blocks: the raw product, plus `x` (a carry
another row hands to this one, 0 for a product's rows), plus the row's
contribution, with its pending carry. -/
structure RowInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (x cb : Nat) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ cb
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  endPtr : k=0 ∨ s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : wv s.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) + x +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

/-- Input arrays remain disjoint from the entire raw product and its counters. -/
theorem input_preserved {m m' : Mem} {B : Addr} {w a i n : Nat}
    (ha : a < 8) (h1 : a ≠ aAcc) (h2 : a ≠ aTmp) (hi : i+n ≤ w)
    (hZ : slot w 8 ≤ (2 : Nat)^64) (hf : Frm B (rowRanges w) m m') :
    wv m' B (slot w a+8*i) n = wv m B (slot w a+8*i) n := by
  obtain sa := slot_le (w := w) ha
  obtain s1 := slot_sep (w := w) h1
  obtain s2 := slot_sep (w := w) h2
  apply hf.wv_eq
  · intro r hr
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;>
      simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc,aTmp] at * <;> omega_using [hi, s1, s2]
  · omega_using [hi, hZ, sa]

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Stream -/
section

/-! The row's loop keeps the eight output words at `d` in the columns. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The raw product with the columns as its eight words at `d`. -/
def streamVal (s : State) (B : Addr) (w d : Nat) : Nat :=
  wv s.mem B (rawBase w) d + 2^(64*d) * cols s +
    2^(64*(d+8)) * wv s.mem B (rawBase w+8*(d+8)) (2*w-(d+8))

/-- As `RowInv`, with the columns the eight words at the block's start and
the pending carry at most `cb`. -/
structure StreamInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (x cb : Nat) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ cb
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  pa : s.gpr .rcx = off B (slot w a+8*i)
  pb : s.gpr .rbp = off B (slot w b+8*(j₀+8*k))
  po : s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : streamVal s B w (i+j₀+8*k) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) + x +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

private theorem stream_arith {L Lo Cs Ct U H A Yb Bk W Q T R cs ct P : Nat}
    (hP : P = Q*T)
    (htile : Lo + R*Ct + R*R*ct = Cs + R*U + A*Bk + R*cs)
    (hinv : L + P*Cs + P*R*(U+R*H) + P*R*cs = W + Q*A*Yb) :
    (L + P*Lo) + P*R*Ct + P*R*R*H + P*R*R*ct = W + Q*A*(Yb + T*Bk) := by
  obtain e1 : P*(Lo + R*Ct + R*R*ct) = P*(Cs + R*U + A*Bk + R*cs) := by rw [htile]
  subst hP
  grind

/-- The value with the columns equal to the memory's eight words at `d`. -/
theorem streamVal_eq {s : State} {B : Addr} {w d : Nat} (hd : d+8 ≤ 2*w)
    (hc : cols s = wv s.mem B (rawBase w+8*d) 8) :
    streamVal s B w d = wv s.mem B (rawBase w) (2*w) := by
  unfold streamVal
  rw [hc,show 2*w = d+(8+(2*w-(d+8))) by omega_using [hd],wv_add,wv_add,
    show rawBase w+8*d+8*8 = rawBase w+8*(d+8) by omega_using [],show d+(8+(2*w-(d+8)))-(d+8) = 2*w-(d+8) by omega_using [],
    show 64*(d+8) = 64*d+64*8 by omega_using [],Nat.pow_add]
  generalize (2 : Nat)^(64*d) = P
  generalize (2 : Nat)^(64*8) = R
  grind

/-- A column block, then a block `blk` that moves the column index to the
next block (any such, setting ZF to `zfv`). -/
theorem streamStep_gen {s₀ s : State} {B : Addr} {Z w a b i j₀ k n x cb : Nat} {mi : BitVec 64}
    {blk : List Instr} {zfv : Bool}
    (hZ : slot w 8 ≤ Z) (_hw : w < (2 : Nat)^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hn : w = j₀+8*n) (hk : k < n)
    (hblk : ∀ u : State, Scr u B Z → u.gpr .rdi = B → Hdr u.mem B w mi →
      word u.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k) →
      WP isa (.block blk) u fun t =>
        t.mem = u.mem.writeW (off B (8*sFn 13)) (BitVec.ofNat 64 (j₀+8*k+8)) ∧ t.zf = some zfv ∧
          Keep [.rax] u t)
    (h : StreamInv s₀ B Z w a b i j₀ k mi x cb s) :
    WP isa (.seq AdxRect8.streamTile (.block blk)) s fun t =>
      t.zf = some zfv ∧ StreamInv s₀ B Z w a b i j₀ (k+1) mi x 2 t := by
  have nowrap := h.scr.nowrap
  obtain Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega_using [hZ, nowrap]
  obtain hj : j₀+8*k+8 ≤ w := by omega_using [hn, hk]
  obtain ar := tile_ranges hi hj ha ha1 ha2
  obtain br := tile_ranges hj hi hb hb1 hb2
  obtain rt := slot_le (w := w) (show aTmp < 8 by decide)
  obtain rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega_using [hZ]
  -- the tile's output words, after the header, the carry slot and the column index
  obtain eOdef : rawBase w+8*(i+j₀+8*k) = slot w aAcc+16+8*(i+(j₀+8*k)) := by unfold rawBase; omega_using []
  obtain po : s.gpr .rsi = off B (slot w aAcc+16+8*(i+(j₀+8*k))) := by rw [← eOdef]; exact h.po
  have prev := h.val
  generalize hd : i+j₀+8*k = d at *
  generalize he : rawBase w+8*d = e at *
  obtain hdw : d+16 ≤ 2*w := by omega_using [hi, hj, hd]
  obtain eH : hdrBytes ≤ e := by rw [← he]; unfold rawBase slot; omega_using []
  obtain eC : carryOffset+8 ≤ e := by rw [← he]; unfold rawBase carryOffset sFn slot hdrBytes aAcc; omega_using []
  obtain eJ : 8*sFn 13+8 ≤ e := by rw [← he]; unfold rawBase sFn slot hdrBytes aAcc; omega_using []
  obtain eI : 8*sFn 12+8 ≤ e := by rw [← he]; unfold rawBase sFn slot hdrBytes aAcc; omega_using []
  obtain eR : rawBase w ≤ e ∧ e+128 ≤ rawBase w+8*(2*w) := by rw [← he]; omega_using [hdw]
  obtain cJ : 8*sFn 13+8 ≤ carryOffset ∨ carryOffset+8 ≤ 8*sFn 13 := by unfold carryOffset sFn; omega_using []
  obtain cI : 8*sFn 12+8 ≤ carryOffset ∨ carryOffset+8 ≤ 8*sFn 12 := by unfold carryOffset sFn; omega_using []
  refine WP.seq (WP.mono (streamTile_ok h.scr h.rdi h.pa h.pb po (by omega_using [hZ, ar]) (by omega_using [hZ, br]) (by omega_using [rawZ, eOdef, eR])
    ar.2.2 (by omega_using [br]) (by rw [← eOdef]; exact eC)) fun u ⟨eq,two,_,fr,pu,bu,ku⟩ => ?_)
  rw [← eOdef] at fr eq pu
  obtain fr3 : Frm B [(e,64),(carryOffset,8),(8*sFn 13,8)] s.mem u.mem := fr.mono (by simp)
  obtain hu : Hdr u.mem B w mi := frame_hdr h.hdr eH fr3
  obtain ju : word u.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k) := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl eJ
      · exact cJ) (by unfold sFn; omega_using [])]
    exact h.indexJ
  obtain iu : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [fr.word_eq (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl eI
      · exact cI) (by unfold sFn; omega_using [])]
    exact h.indexI
  refine WP.mono (hblk u (h.scr.congr ku.2.2) ((ku.gpr (by decide)).trans h.rdi) hu ju)
    fun t ⟨mt,zt,kt⟩ => ?_
  obtain ot : Outside B (8*sFn 13) 8 u.mem t.mem := by
    rw [mt]; exact writeW_outside _ _ _ (by unfold sFn; omega_using [])
  obtain toU : Frm B (rowRanges w) s.mem u.mem := by
    intro x hx
    apply fr x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    obtain a0 := hx (rawBase w,16*w) (by simp [rowRanges])
    obtain a1 := hx (carryOffset,8) (by simp [rowRanges])
    rcases hr with rfl | rfl
    · simp only [] at a0 ⊢; omega_using [eR, a0]
    · exact a1
  obtain wider : Frm B (rowRanges w) s.mem t.mem := toU.trans (Frm.of_outside ot (by simp [rowRanges]))
  obtain va := input_preserved ha ha1 ha2 hi Z64 h.frame
  obtain vb := input_preserved hb hb1 hb2 hj Z64 h.frame
  obtain ct : word t.mem B carryOffset = word u.mem B carryOffset :=
    ot.word cJ.symm (by omega_using [Z64, br, eOdef, eC])
  obtain colsT : cols t = cols u := cols_keep kt (by decide)
  refine ⟨?_,⟨h.scr.congr (ku.trans kt).2.2,frame_hdr (n := 64) hu eH (Frm.of_outside ot (by simp)),
    (kt.gpr (by decide)).trans ((ku.gpr (by decide)).trans h.rdi),?_,?_,by rw [ct]; exact two,
    (h.keep.trans (ku.trans kt)).mono (by decide),h.frame.trans wider,
    (kt.gpr (by decide)).trans ((ku.gpr (by decide)).trans h.pa),?_,?_,?_⟩⟩
  · exact zt
  · rw [ot.word (by unfold sFn; omega_using []) (by unfold sFn; omega_using [])]; exact iu
  · rw [mt,word_writeW_self,show j₀+8*(k+1) = j₀+8*k+8 by omega_using []]
  · rw [kt.gpr (by decide),bu]
    exact congrArg (off B) (by omega_using [])
  · rw [kt.gpr (by decide),pu,show i+j₀+8*(k+1) = d+8 by omega_using [hd],← he]
    exact congrArg (off B) (by omega_using [])
  · have below : wv t.mem B (rawBase w) d = wv s.mem B (rawBase w) d := by
      rw [ot.wv (by unfold rawBase slot sFn hdrBytes aAcc; omega_using []) (by omega_using [Z64, br, he, eOdef])]
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inl (by simp only []; omega_using [he])
        · exact Or.inr (by simp only []; unfold rawBase slot hdrBytes aAcc carryOffset sFn; omega_using [])) (by omega_using [Z64, br, he, eOdef])
    obtain above : wv t.mem B (e+128) (2*w-(d+16)) = wv s.mem B (e+128) (2*w-(d+16)) := by
      rw [ot.wv (by omega_using [eJ]) (by omega_using [nowrap, rawZ, he, eR])]
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inr (by simp only []; omega_using [])
        · exact Or.inr (by simp only []; omega_using [eC])) (by omega_using [nowrap, rawZ, he, eR])
    obtain upper : wv u.mem B (e+64) 8 = wv s.mem B (e+64) 8 := by
      exact fr.wv_eq (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact Or.inr (by simp only []; omega_using [])
        · exact Or.inr (by simp only []; omega_using [eC])) (by omega_using [Z64, br, eOdef])
    obtain lowT : wv t.mem B e 8 = wv u.mem B e 8 := ot.wv (by omega_using [eJ]) (by omega_using [Z64, br, eOdef])
    obtain hsplit : streamVal s B w d = wv s.mem B (rawBase w) d + 2^(64*d) * cols s +
        2^(64*d) * 2^512 * (wv s.mem B (e+64) 8 + 2^512 * wv s.mem B (e+128) (2*w-(d+16))) := by
      unfold streamVal
      rw [show 2*w-(d+8) = 8+(2*w-(d+16)) by omega_using [hdw],wv_add,
        show rawBase w+8*(d+8) = e+64 by omega_using [he],show e+64+8*8 = e+128 by omega_using [],
        show 64*(d+8) = 64*d+512 by omega_using [],Nat.pow_add,show (64 : Nat)*8 = 512 from rfl]
    obtain tsplit : streamVal t B w (d+8) = (wv s.mem B (rawBase w) d +
          2^(64*d) * wv u.mem B e 8) + 2^(64*d) * 2^512 * cols u +
        2^(64*d) * 2^512 * 2^512 * wv s.mem B (e+128) (2*w-(d+16)) := by
      unfold streamVal
      rw [wv_add,below,he,lowT,colsT,show rawBase w+8*(d+8+8) = e+128 by omega_using [he],
        show 2*w-(d+8+8) = 2*w-(d+16) by omega_using [],above,
        show 64*(d+8) = 64*d+512 by omega_using [],show 64*(d+8+8) = 64*d+512+512 by omega_using [],
        Nat.pow_add,Nat.pow_add,Nat.pow_add]
    obtain bk : wv s₀.mem B (slot w b+8*j₀) (8*(k+1)) = wv s₀.mem B (slot w b+8*j₀) (8*k) +
        2^(64*(8*k)) * wv s.mem B (slot w b+8*(j₀+8*k)) 8 := by
      rw [show 8*(k+1) = 8*k+8 by omega_using [],wv_add,show slot w b+8*j₀+8*(8*k) = slot w b+8*(j₀+8*k) by omega_using [],vb]
    rw [show i+j₀+8*(k+1) = d+8 by omega_using [hd],show i+j₀+8*(k+1+1) = d+8+8 by omega_using [hd],ct,bk,tsplit,
      show 64*(d+8+8) = 64*d+512+512 by omega_using [],Nat.pow_add,Nat.pow_add]
    rw [show i+j₀+8*(k+1) = d+8 by omega_using [hd],hsplit,show 64*(d+8) = 64*d+512 by omega_using [],Nat.pow_add] at prev
    rw [va] at eq
    obtain hPQ : (2 : Nat)^(64*d) = 2^(64*(i+j₀)) * 2^(64*(8*k)) := by
      rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega_using [hd])
    generalize (2 : Nat)^512 = R at eq prev ⊢
    generalize (2 : Nat)^(64*d) = P at hPQ prev ⊢
    exact stream_arith hPQ eq prev

theorem streamStep_inv {s₀ s : State} {B : Addr} {Z w a b i j₀ k n x cb : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w < (2 : Nat)^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hn : w = j₀+8*n) (hk : k < n)
    (h : StreamInv s₀ B Z w a b i j₀ k mi x cb s) :
    WP isa AdxRect8.rowStep s fun t =>
      t.zf = some (decide (k+1=n)) ∧ StreamInv s₀ B Z w a b i j₀ (k+1) mi x 2 t := by
  unfold AdxRect8.rowStep
  refine WP.mono (streamStep_gen hZ hw hi ha hb ha1 ha2 hb1 hb2 hn hk
    (fun u hs hd hh hj => nextColumn_ok hs hd hh hZ (by omega_using [hw, hn, hk]) (by omega_using [hw]) hj) h) fun t ⟨zt,ht⟩ => ⟨?_,ht⟩
  rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega_using [hn]))

end VG.Proof.Bignum.X86_64.AdxRect8

end

/-! ## AdxRect8Row -/
section

/-! Correctness and termination of a complete rectangular row. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.Bignum.X86_64.AdxRotate8 (cols cols_keep)
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

/-- The row's columns loaded, after `setup`: the loop's state before its first
column block, for any `s₀` with `u`'s memory and registers but those `setup`
sets. -/
theorem rowLoad_ok {s₀ u : State} {B : Addr} {Z w a b i j₀ : Nat} {mi : BitVec 64}
    (hs : Scr u B Z) (hd : u.gpr .rdi = B) (hh : Hdr u.mem B w mi) (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w)
    (hj : j₀+8 ≤ w)
    (hidx : word u.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word u.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word u.mem B carryOffset).toNat = 0)
    (ua : u.gpr .rcx = off B (slot w a+8*i)) (ub : u.gpr .rbp = off B (slot w b+8*j₀))
    (uo : u.gpr .rsi = off B (slot w aAcc+16+8*(i+j₀)))
    (hm : u.mem = s₀.mem) (hk : Keep mmRegs s₀ u) :
    WP isa (.block AdxRotate8.loadCols) u (StreamInv s₀ B Z w a b i j₀ 0 mi 0 2) := by
  have nowrap := hs.nowrap
  obtain rt := slot_le (w := w) (show aTmp < 8 by decide)
  obtain rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega_using [hZ]
  obtain uo' : u.gpr .rsi = off B (rawBase w+8*(i+j₀+8*0)) := by
    rw [uo]; exact congrArg (off B) (by unfold rawBase; omega_using [])
  refine WP.mono (AdxRotate8.loadCols_ok hs uo' (by omega_using [hi, hj, rawZ])) fun v ⟨cv,kv⟩ => ?_
  have mv : v.mem = u.mem := kv.2.1
  exact ⟨hs.congr kv.2.2.2,mv ▸ hh,(kv.1 .rdi (by decide)).trans hd,mv ▸ hidx,
    by simpa only [Nat.mul_zero,Nat.add_zero,mv] using hjdx,by rw [mv,hc]; omega_using [],
    (hk.trans kv.keep).mono (by decide),by rw [mv,hm]; exact Frm.refl _ _ _,
    (kv.1 .rcx (by decide)).trans ua,by rw [kv.1 .rbp (by decide),ub]; simp only [Nat.mul_zero,Nat.add_zero],
    (kv.1 .rsi (by decide)).trans uo',by
      rw [streamVal_eq (by omega_using [hi, hj]) (by rw [cv,mv]),mv,hc,hm]
      simp only [Nat.mul_zero,Nat.add_zero,wv]⟩

/-- The columns stored after the loop's last column block. -/
theorem rowEnd_ok {s₀ t : State} {B : Addr} {Z w a b i j₀ n x cb : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hi : i+8 ≤ w) (hwN : w = j₀+8*n)
    (ht : StreamInv s₀ B Z w a b i j₀ n mi x cb t) :
    WP isa (.block AdxRotate8.storeCols) t (RowInv s₀ B Z w a b i j₀ n mi x cb) := by
  obtain rt := slot_le (w := w) (show aTmp < 8 by decide)
  obtain rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega_using [hZ]
  have tnow := ht.scr.nowrap
  obtain hDw : i+j₀+8*n+8 ≤ 2*w := by omega_using [hi, hwN]
  obtain oI : 8*sFn 12+8 ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase sFn slot hdrBytes aAcc; omega_using []
  obtain oJ : 8*sFn 13+8 ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase sFn slot hdrBytes aAcc; omega_using []
  obtain oC : carryOffset+8 ≤ rawBase w+8*(i+j₀+8*n) := by
    unfold rawBase carryOffset sFn slot hdrBytes aAcc; omega_using []
  obtain oH : hdrBytes ≤ rawBase w+8*(i+j₀+8*n) := by unfold rawBase slot; omega_using []
  obtain small : 8*sFn 13+8 ≤ 2^64 ∧ 8*sFn 12+8 ≤ 2^64 ∧ carryOffset+8 ≤ 2^64 := by
    unfold carryOffset sFn; omega_using []
  refine WP.mono (AdxRotate8.storeCols_ok ht.scr ht.po (by omega_using [rawZ, hDw])) fun x ⟨vx,ox,kx⟩ => ?_
  obtain fx : Frm B (rowRanges w) t.mem x.mem := by
    intro y hy
    apply ox y
    obtain a0 := hy (rawBase w,16*w) (by simp [rowRanges])
    simp only [] at a0 ⊢
    omega_using [hDw, a0]
  refine ⟨ht.scr.congr kx.2.2,ht.hdr.of_outside ox oH,
    (kx.gpr (by simp)).trans ht.rdi,?_,?_,?_,(ht.keep.trans kx).mono (by simp),ht.frame.trans fx,
    Or.inr ((kx.gpr (by simp)).trans ht.po),?_⟩
  · rw [ox.word (Or.inl oI) small.2.1]; exact ht.indexI
  · rw [ox.word (Or.inl oJ) small.1]; exact ht.indexJ
  · rw [ox.word (Or.inl oC) small.2.2]; exact ht.carry
  · have val := ht.val
    rw [ox.word (Or.inl oC) small.2.2]
    obtain same : streamVal x B w (i+j₀+8*n) = streamVal t B w (i+j₀+8*n) := by
      unfold streamVal
      rw [cols_keep kx (by decide),ox.wv (Or.inl (by omega_using [])) (by omega_using [rawZ, tnow, hDw]),ox.wv (Or.inr (by omega_using [])) (by omega_using [rawZ, tnow, hDw])]
    rw [← streamVal_eq hDw (by rw [cols_keep kx (by decide),vx]),same]
    exact val


theorem row_ok {s : State} {B : Addr} {Z w a b i j₀ n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hh : Hdr s.mem B w mi)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {ca cb : Nat} (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (hZ : slot w 8 ≤ Z) (hw : w < 2^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hwN : w = j₀+8*n) (hn : 0 < n)
    (hidx : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i)
    (hjdx : word s.mem B (8*sFn 13) = BitVec.ofNat 64 j₀)
    (hc : (word s.mem B carryOffset).toNat = 0) :
    WP isa (AdxRect8.row ca cb) s (RowInv s B Z w a b i j₀ n mi 0 2) := by
  unfold AdxRect8.row
  refine WP.seq (WP.mono (setup_ok hs hd hh hZ hv pa pb hidx hjdx) fun u ⟨ua,ub,uo,um,ku⟩ => ?_)
  refine WP.seq (WP.mono (rowLoad_ok (s₀ := s) (hs.congr ku.2.2) ((ku.gpr (by decide)).trans hd) (um ▸ hh) hZ hi
    (by omega_using [hwN, hn]) (um ▸ hidx) (um ▸ hjdx) (um ▸ hc) ua ub uo um (ku.mono (by decide))) fun v hv0 => ?_)
  exact WP.seq (WP.mono (wp_upto (a := 0) (N := n) (Q := StreamInv s B Z w a b i j₀ n mi 0 2) hn
    (StreamInv s B Z w a b i j₀ · mi 0 2)
    (fun _ _ hk _ h => streamStep_inv hZ hw hi ha hb ha1 ha2 hb1 hb2 hwN hk h)
    (fun _ h => h) hv0) fun t ht => rowEnd_ok hZ hi hwN ht)

end VG.Proof.Bignum.X86_64.AdxRect8

end
