import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Impl.Bignum.X86_64.AdxRect8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddInput
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt

/-! ## AdxRect8Product -/
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
    refine WP.seq (WP.mono (ih (by omega) (by omega) (by omega) (by omega)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    refine WP.mono (productStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho)
      (by omega) (by omega) hnZ) fun t ⟨vt, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
    have mu : word a.mem B (eU + 8 * n) = word s.mem B (eU + 8 * n) := oa.word (by omega) (by omega)
    have lo : wv t.mem B eO n = wv a.mem B eO n := ot.wv (by omega) (by omega)
    refine ⟨?_, (oa.mono (o' := eO) (n' := 8 * (n + 1)) (by omega) (by omega)).trans
      (ot.mono (o' := eO) (n' := 8 * (n + 1)) (by omega) (by omega)), (ka.trans kt).mono (by decide)⟩
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
  refine WP.seq (WP.mono (productN_disjoint_ok (n := 8) hs ha hb ho (by omega) (by omega) hB
    (by omega) (by omega)) fun a ⟨ea,oa,ka⟩ => ?_)
  refine WP.seq (WP.mono (upper_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hd)
    ((ka.gpr (by decide)).trans ho) (by omega)) fun b ⟨db,pb,mb,kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.seq (WP.mono (AdxDualAdd.addInput_ok (hs.congr kab.2.2) pb (by omega))
    fun c ⟨ec,bc,_,_,kc⟩ => ?_)
  have kabc := kab.trans kc.keep
  refine WP.mono (streamEnd_ok (hs.congr kabc.2.2) ((kabc.gpr (by decide)).trans hd)
    ((kabc.gpr (by decide)).trans hb) (by omega)) fun t ⟨wt,ot,pt,kt⟩ => ?_
  have carryA : word a.mem B carryOffset = word s.mem B carryOffset :=
    oa.word (by omega) (by omega)
  have upperA : wv a.mem B (eO+64) 8 = wv s.mem B (eO+64) 8 :=
    oa.wv (by omega) (by omega)
  have lowT : wv t.mem B eO 8 = wv a.mem B eO 8 := by
    rw [ot.wv (by omega) (by omega),kc.2.1,mb]
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
    hs.ld (by have := hdr_lt_slot w 8 hk; omega)
  refine WP.mono (WP.keep [.rax,.rdx,.rcx,.rbp,.rsi] (Q := fun t =>
    t.gpr .rcx = off B (slot w a+8*i) ∧
    t.gpr .rbp = off B (slot w b+8*j) ∧
    t.gpr .rsi = off B (slot w aAcc+16+8*(i+j)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hc,hp,ho,hm⟩,k⟩ => ⟨hc,hp,ho,hm,k⟩
  unfold AdxRect8.setup
  xrun [State.ea,hdr,hd,hdrOff,hl (sFn 12) (by decide),hl (sFn 13) (by decide),
    hl (sArr ca) (by have := hv.lt pa; unfold sArr; omega),hl (sArr cb) (by have := hv.lt pb; unfold sArr; omega),
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
