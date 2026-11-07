module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Kernel
public import VerifiedGarbage.Impl.MlDsa.PPC64LE.PreparedKey
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Base
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Piece
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Contracts
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.ContractsV
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Site
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallSP
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Sign.Lay
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Impl.Gather.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# ML-DSA on PPC64LE: preparing keys

`vg_mldsa*_prepare_signing_key` and `vg_mldsa*_prepare_verifying_key`
(`Impl/MlDsa/PPC64LE/PreparedKey.lean`) meet `prepareSecretKeyContract` and
`preparePublicKeyContract`. In the frames of `frames3` (`Kernel.lean`), with
`prepared` in `r30` and `scratch` in `r31`: the encoded key copied
(`setup_ok`), then each polynomial `i` (`PI`, `step_ok`): unpacked from the
copy to its slot (`bu_call`, `t1_call`) and transformed there (`ntt_call`).
Every call's arguments depend only on the pointers, so two runs leak the same
(`prepare_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.PreparedKey

open VG VG.PPC64LE
open VG.PPC64LE.RegUpd (gpr_write_self gpr_write_of_ne)
open VG.Proof.MlDsa.PPC64LE.KeyGen (reg Callee callV callV_tr CallRel glueOk glueSt glueSt_arg glueSt_rd glueSt_wr
  glueSt_sp glueSt_mem view view_gpr view_glue_sp view_glue_mem imm_toNat imm32 imm32_toNat argOk_imm)
open VG.Impl.MlDsa.PPC64LE.KeyGen (Arg callAt seqR)
open VG.Impl.MlDsa.PPC64LE.PreparedKey
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The calls -/

section
variable {s : State} {P : Addr} {PB : Nat}

theorem covers_sub {o l : Nat} (h : o + l ≤ PB) {rs : List Region} (hm : reg P PB ∈ rs) :
    Covers [reg (P + BitVec.ofNat 64 o) l] rs :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨reg P PB, hm, o, rfl, h⟩

theorem fit_sub {o l : Nat} (h : o + l ≤ PB) (hl : 0 < l) (fP : P.toNat + PB ≤ 2 ^ 64) :
    (P + BitVec.ofNat 64 o).toNat + l ≤ 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : o < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mod_le _ _) _) (by omega)

theorem view_ptr {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d b : Reg}
    {o : Nat} (hm : (d, .ptr (b, o)) ∈ as) (hd : d ∉ linkRegs) (rd wr : List Region) :
    (view (glueSt s as) rd wr).gpr d = s.gpr b + BitVec.ofNat 64 o := by
  rw [view_gpr _ _ _ hd, glueSt_arg s hg hn hm]; rfl

theorem view_imm {as : List (Reg × Arg)} (hg : glueOk as = true) (hn : (as.map Prod.fst).Nodup) {d : Reg}
    {v : Nat} (hm : (d, .imm v) ∈ as) (hd : d ∉ linkRegs) (rd wr : List Region) :
    (view (glueSt s as) rd wr).gpr d = BitVec.ofNat 64 v := by
  rw [view_gpr _ _ _ hd, glueSt_arg s hg hn hm]; rfl

end

theorem below0 (sp : Addr) (r : Region) : (below sp 0).Disjoint r := fun _ h _ => by
  simp only [Region.Contains] at h; omega

/-! ### `vg_mldsa_bit_unpack` -/

/-- Its arguments: `len` bytes at `prepared + o`, to `prepared + q`. -/
abbrev buAs (o len a b q : Nat) : List (Reg × Arg) :=
  [(.r3, .ptr (.r30, o)), (.r4, .imm len), (.r5, .imm a), (.r6, .imm b), (.r7, .ptr (.r30, q))]

/-- What a call of `vg_mldsa_bit_unpack` needs: the slot after the bytes, in `prepared`. -/
structure BuArgs (PB o len a b q : Nat) : Prop where
  oq : o + len ≤ q
  qb : q + 1024 ≤ PB
  ab : (a, b) ∈ bitPackParams
  hl : len = 32 * bitlen (a + b)
  lt : 0 < len ∧ len < 2 ^ 31 ∧ a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ q < 2 ^ 31

theorem BuArgs.hg {PB o len a b q : Nat} (m : BuArgs PB o len a b q) : glueOk (buAs o len a b q) = true := by
  obtain ⟨-, l1, l2, l3, l4⟩ := m.lt
  have : o < 2 ^ 31 := by have := m.oq; omega
  simp [glueOk, KeyGen.argReg, KeyGen.argOk, l1, l2, l3, l4, this]

theorem bu_pre' {s : State} {P : Addr} {PB o len a b q : Nat} (h30 : s.gpr .r30 = P) (wP : reg P PB ∈ s.wr)
    (fP : P.toNat + PB ≤ 2 ^ 64) (m : BuArgs PB o len a b q) :
    (bitUnpackContract PPC64LE.abi 0).pre (KeyGen.view (glueSt s (buAs o len a b q))
      [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]) ∧
    Covers ([reg (P + BitVec.ofNat 64 o) len] ++ [reg (P + BitVec.ofNat 64 q) 1024]) (s.rd ++ s.wr) ∧
    Covers [reg (P + BitVec.ofNat 64 q) 1024] s.wr := by
  obtain ⟨l0, l1, l2, l3, l4⟩ := m.lt
  have hn : ((buAs o len a b q).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  have g3 := view_ptr (s := s) m.hg hn (d := .r3) (b := .r30) (o := o) (by simp) (by decide)
    [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]
  have g4 := view_imm (s := s) m.hg hn (d := .r4) (v := len) (by simp) (by decide)
    [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]
  have g5 := view_imm (s := s) m.hg hn (d := .r5) (v := a) (by simp) (by decide)
    [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]
  have g6 := view_imm (s := s) m.hg hn (d := .r6) (v := b) (by simp) (by decide)
    [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]
  have g7 := view_ptr (s := s) m.hg hn (d := .r7) (b := .r30) (o := q) (by simp) (by decide)
    [reg (P + BitVec.ofNat 64 o) len] [reg (P + BitVec.ofNat 64 q) 1024]
  rw [h30] at g3 g7
  have hoq := m.oq; have hqb := m.qb
  have hoP : o + len ≤ PB := by omega
  have e5 : ((KeyGen.view (glueSt s (buAs o len a b q)) [reg (P + BitVec.ofNat 64 o) len]
      [reg (P + BitVec.ofNat 64 q) 1024]).gpr .r5).setWidth 32 = BitVec.ofNat 32 a := by
    rw [g5]; exact imm32 (by omega)
  have e6 : ((KeyGen.view (glueSt s (buAs o len a b q)) [reg (P + BitVec.ofNat 64 o) len]
      [reg (P + BitVec.ofNat 64 q) 1024]).gpr .r6).setWidth 32 = BitVec.ofNat 32 b := by
    rw [g6]; exact imm32 (by omega)
  have tl : (BitVec.ofNat 64 len).toNat = len := imm_toNat (by omega)
  have ta : (BitVec.ofNat 32 a).toNat = a := imm32_toNat (by omega)
  have tb : (BitVec.ofNat 32 b).toNat = b := imm32_toNat (by omega)
  refine ⟨KeyGen.bu_pre (stk := 0) g3 g4 e5 e6 g7 (by rw [State.withRegions_rd, tl]) rfl (Nat.zero_le _)
    (by rw [tl]; exact Offset.disjoint _ (.inl hoq) (by omega) (by omega))
    (below0 _ _) (below0 _ _)
    (by rw [tl]; exact fit_sub hoP l0 fP) (fit_sub hqb (by decide) fP)
    (by rw [ta, tb]; exact m.ab) (by rw [tl, ta, tb]; exact m.hl), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg P PB, List.mem_append_right _ wP, o, rfl, by omega⟩
    · exact ⟨reg P PB, List.mem_append_right _ wP, q, rfl, hqb⟩
  · exact covers_sub hqb wP

theorem BuArgs.vals {s : State} {PB o len a b q : Nat} (m : BuArgs PB o len a b q) (rd wr : List Region) :
    (KeyGen.view (glueSt s (buAs o len a b q)) rd wr).gpr .r3 = s.gpr .r30 + BitVec.ofNat 64 o ∧
    (KeyGen.view (glueSt s (buAs o len a b q)) rd wr).gpr .r4 = BitVec.ofNat 64 len ∧
    (KeyGen.view (glueSt s (buAs o len a b q)) rd wr).gpr .r5 = BitVec.ofNat 64 a ∧
    (KeyGen.view (glueSt s (buAs o len a b q)) rd wr).gpr .r6 = BitVec.ofNat 64 b ∧
    (KeyGen.view (glueSt s (buAs o len a b q)) rd wr).gpr .r7 = s.gpr .r30 + BitVec.ofNat 64 q := by
  have hn : ((buAs o len a b q).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  exact ⟨view_ptr m.hg hn (d := .r3) (b := .r30) (o := o) (by simp) (by decide) _ _,
    view_imm m.hg hn (d := .r4) (v := len) (by simp) (by decide) _ _,
    view_imm m.hg hn (d := .r5) (v := a) (by simp) (by decide) _ _,
    view_imm m.hg hn (d := .r6) (v := b) (by simp) (by decide) _ _,
    view_ptr m.hg hn (d := .r7) (b := .r30) (o := q) (by simp) (by decide) _ _⟩

theorem bu_post' {s s' : State} {P : Addr} {o len a b q : Nat} (h30 : s.gpr .r30 = P)
    {PB : Nat} (m : BuArgs PB o len a b q) {rd wr : List Region}
    (hp : (bitUnpackContract PPC64LE.abi 0).post (KeyGen.view (glueSt s (buAs o len a b q)) rd wr)
      (s'.withRegions rd wr)) :
    PolyIs s'.mem (P + BitVec.ofNat 64 q) (toRq (bitUnpack (bytesAt s.mem (P + BitVec.ofNat 64 o) len) a b)) := by
  obtain ⟨l0, l1, l2, l3, l4⟩ := m.lt
  obtain ⟨g3, g4, g5, g6, g7⟩ := m.vals (s := s) rd wr
  have := KeyGen.bu_post hp
  rwa [State.withRegions_mem, g3, g4, g5, g6, g7, view_glue_mem, h30, imm32 (by omega), imm32 (by omega),
    imm32_toNat (by omega), imm32_toNat (by omega), imm_toNat (by omega)] at this

theorem bu_pub' {x y : State} {o len a b q : Nat} {PB : Nat} (m : BuArgs PB o len a b q)
    (hsp : x.sp = y.sp) (h30 : x.gpr .r30 = y.gpr .r30) {rd wr rd' wr' : List Region} :
    (bitUnpackContract PPC64LE.abi 0).pub (KeyGen.view (glueSt x (buAs o len a b q)) rd wr)
      (KeyGen.view (glueSt y (buAs o len a b q)) rd' wr') := by
  obtain ⟨x3, x4, x5, x6, x7⟩ := m.vals (s := x) rd wr
  obtain ⟨y3, y4, y5, y6, y7⟩ := m.vals (s := y) rd' wr'
  exact KeyGen.bu_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [x3, y3, h30]) (by rw [x4, y4])
    (by rw [x5, y5]) (by rw [x6, y6]) (by rw [x7, y7, h30])

/-! ### `vg_mldsa_unpack_t1` -/

/-- Its arguments: the 320 bytes at `prepared + o`, to `prepared + q`. -/
abbrev t1As (o q : Nat) : List (Reg × Arg) := [(.r3, .ptr (.r30, o)), (.r4, .ptr (.r30, q))]

structure T1Args (PB o q : Nat) : Prop where
  oq : o + 320 ≤ q
  qb : q + 1024 ≤ PB
  lt : q < 2 ^ 31

theorem T1Args.hg {PB o q : Nat} (m : T1Args PB o q) : glueOk (t1As o q) = true := by
  have := m.lt; have := m.oq
  have : o < 2 ^ 31 := by omega
  simp [glueOk, KeyGen.argReg, KeyGen.argOk, m.lt, this]

theorem T1Args.vals {s : State} {PB o q : Nat} (m : T1Args PB o q) (rd wr : List Region) :
    (KeyGen.view (glueSt s (t1As o q)) rd wr).gpr .r3 = s.gpr .r30 + BitVec.ofNat 64 o ∧
    (KeyGen.view (glueSt s (t1As o q)) rd wr).gpr .r4 = s.gpr .r30 + BitVec.ofNat 64 q := by
  have hn : ((t1As o q).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  exact ⟨view_ptr m.hg hn (d := .r3) (b := .r30) (o := o) (by simp) (by decide) _ _,
    view_ptr m.hg hn (d := .r4) (b := .r30) (o := q) (by simp) (by decide) _ _⟩

theorem t1_pre' {s : State} {P : Addr} {PB o q : Nat} (h30 : s.gpr .r30 = P) (wP : reg P PB ∈ s.wr)
    (fP : P.toNat + PB ≤ 2 ^ 64) (m : T1Args PB o q) :
    (unpackT1Contract PPC64LE.abi 0).pre (KeyGen.view (glueSt s (t1As o q))
      [reg (P + BitVec.ofNat 64 o) 320] [reg (P + BitVec.ofNat 64 q) 1024]) ∧
    Covers ([reg (P + BitVec.ofNat 64 o) 320] ++ [reg (P + BitVec.ofNat 64 q) 1024]) (s.rd ++ s.wr) ∧
    Covers [reg (P + BitVec.ofNat 64 q) 1024] s.wr := by
  obtain ⟨g3, g4⟩ := m.vals (s := s) [reg (P + BitVec.ofNat 64 o) 320] [reg (P + BitVec.ofNat 64 q) 1024]
  rw [h30] at g3 g4
  have hoq := m.oq; have hqb := m.qb
  refine ⟨KeyGen.t1_pre (stk := 0) g3 g4 rfl rfl (Nat.zero_le _)
    (Offset.disjoint _ (.inl hoq) (by omega) (by omega)) (below0 _ _) (below0 _ _)
    (fit_sub (by omega) (by decide) fP) (fit_sub hqb (by decide) fP), ?_, ?_⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg P PB, List.mem_append_right _ wP, o, rfl, by show o + 320 ≤ PB; omega⟩
    · exact ⟨reg P PB, List.mem_append_right _ wP, q, rfl, hqb⟩
  · exact covers_sub hqb wP

theorem t1_post' {s s' : State} {P : Addr} {PB o q : Nat} (h30 : s.gpr .r30 = P) (m : T1Args PB o q)
    {rd wr : List Region}
    (hp : (unpackT1Contract PPC64LE.abi 0).post (KeyGen.view (glueSt s (t1As o q)) rd wr) (s'.withRegions rd wr)) :
    PolyIs s'.mem (P + BitVec.ofNat 64 q)
      ((simpleBitUnpack (bytesAt s.mem (P + BitVec.ofNat 64 o) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  obtain ⟨g3, g4⟩ := m.vals (s := s) rd wr
  have := KeyGen.t1_post hp
  rwa [State.withRegions_mem, g3, g4, view_glue_mem, h30] at this

theorem t1_pub' {x y : State} {PB o q : Nat} (m : T1Args PB o q) (hsp : x.sp = y.sp) (h30 : x.gpr .r30 = y.gpr .r30)
    {rd wr rd' wr' : List Region} :
    (unpackT1Contract PPC64LE.abi 0).pub (KeyGen.view (glueSt x (t1As o q)) rd wr)
      (KeyGen.view (glueSt y (t1As o q)) rd' wr') := by
  obtain ⟨x3, x4⟩ := m.vals (s := x) rd wr
  obtain ⟨y3, y4⟩ := m.vals (s := y) rd' wr'
  exact KeyGen.t1_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [x3, y3, h30]) (by rw [x4, y4, h30])

/-! ### `vg_mldsa_ntt` -/

/-- Its arguments: the slot at `prepared + q`, and `scratch`. -/
abbrev ntAs (q : Nat) : List (Reg × Arg) := [(.r3, .ptr (.r30, q)), (.r4, .ptr (.r31, 0))]

theorem ntAs_hg {q : Nat} (h : q < 2 ^ 31) : glueOk (ntAs q) = true := by
  simp [glueOk, KeyGen.argReg, KeyGen.argOk, h]

theorem ntAs_vals {s : State} {q : Nat} (h : q < 2 ^ 31) (rd wr : List Region) :
    (KeyGen.view (glueSt s (ntAs q)) rd wr).gpr .r3 = s.gpr .r30 + BitVec.ofNat 64 q ∧
    (KeyGen.view (glueSt s (ntAs q)) rd wr).gpr .r4 = s.gpr .r31 := by
  have hn : ((ntAs q).map Prod.fst).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  refine ⟨view_ptr (ntAs_hg h) hn (d := .r3) (b := .r30) (o := q) (by simp) (by decide) _ _, ?_⟩
  rw [view_ptr (ntAs_hg h) hn (d := .r4) (b := .r31) (o := 0) (by simp) (by decide) _ _, BitVec.add_zero]

theorem nt_pre' {s : State} {P C : Addr} {PB q : Nat} (h30 : s.gpr .r30 = P) (h31 : s.gpr .r31 = C)
    (wP : reg P PB ∈ s.wr) (wC : reg C 1024 ∈ s.wr) (dPC : (reg P PB).Disjoint (reg C 1024))
    (fP : P.toNat + PB ≤ 2 ^ 64) (fC : C.toNat + 1024 ≤ 2 ^ 64) (hq : q + 1024 ≤ PB) (hq31 : q < 2 ^ 31)
    (hsp : 96 ≤ s.sp.toNat) (bP : (below s.sp 96).Disjoint (reg P PB)) (bC : (below s.sp 96).Disjoint (reg C 1024))
    (hr : Reduced s.mem (P + BitVec.ofNat 64 q)) :
    (nttContract PPC64LE.abi 96).pre (KeyGen.view (glueSt s (ntAs q)) []
      [reg (P + BitVec.ofNat 64 q) 1024, reg C 1024]) ∧
    Covers ([] ++ [reg (P + BitVec.ofNat 64 q) 1024, reg C 1024]) (s.rd ++ s.wr) ∧
    Covers [reg (P + BitVec.ofNat 64 q) 1024, reg C 1024] s.wr := by
  obtain ⟨g3, g4⟩ := ntAs_vals (s := s) hq31 [] [reg (P + BitVec.ofNat 64 q) 1024, reg C 1024]
  rw [h30] at g3; rw [h31] at g4
  have sq : Region.Sub (reg (P + BitVec.ofNat 64 q) 1024) (reg P PB) := Offset.sub_base _ hq
  have cw : Covers [reg (P + BitVec.ofNat 64 q) 1024, reg C 1024] s.wr := Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨reg P PB, wP, q, rfl, hq⟩
    · exact ⟨reg C 1024, wC, 0, by simp, by simp⟩
  refine ⟨KeyGen.ip_pre (stk := 96) g3 g4 rfl rfl (by rw [view_glue_sp]; exact hsp) (dPC.sub_left sq)
    (by rw [view_glue_sp]; exact bP.sub_right sq) (by rw [view_glue_sp]; exact bC) (fit_sub hq (by decide) fP) fC
    (by rw [view_glue_mem]; exact hr), ?_, cw⟩
  intro a n hi
  obtain ⟨r, hr, hc⟩ := cw a n (by simpa using hi)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem nt_post' {s s' : State} {P : Addr} {q : Nat} (h30 : s.gpr .r30 = P) (hq31 : q < 2 ^ 31)
    {rd wr : List Region}
    (hp : (nttContract PPC64LE.abi 96).post (KeyGen.view (glueSt s (ntAs q)) rd wr) (s'.withRegions rd wr)) :
    PolyIs s'.mem (P + BitVec.ofNat 64 q) (ntt (polyAt s.mem (P + BitVec.ofNat 64 q))) := by
  obtain ⟨g3, -⟩ := ntAs_vals (s := s) hq31 rd wr
  have := KeyGen.ip_post hp
  rwa [State.withRegions_mem, g3, view_glue_mem, h30] at this

theorem nt_pub' {x y : State} {q : Nat} (hq31 : q < 2 ^ 31) (hsp : x.sp = y.sp) (h30 : x.gpr .r30 = y.gpr .r30)
    (h31 : x.gpr .r31 = y.gpr .r31) {rd wr rd' wr' : List Region} :
    (nttContract PPC64LE.abi 96).pub (KeyGen.view (glueSt x (ntAs q)) rd wr) (KeyGen.view (glueSt y (ntAs q)) rd' wr') := by
  obtain ⟨x3, x4⟩ := ntAs_vals (s := x) hq31 rd wr
  obtain ⟨y3, y4⟩ := ntAs_vals (s := y) hq31 rd' wr'
  exact KeyGen.ip_pub (by rw [view_glue_sp, view_glue_sp, hsp]) (by rw [x3, y3, h30]) (by rw [x4, y4, h31])

/-! ## The function's precondition, and what holds of the polynomials done -/

/-- The precondition of a preparation, with the key's `KL` bytes, the
prepared key's `PB` and `K` bytes of stack. -/
structure PPre (KL PB K : Nat) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (σ.gpr .r3) KL]
  wr : σ.wr = [reg (σ.gpr .r4) PB, reg (σ.gpr .r5) 1024]
  d_kp : (reg (σ.gpr .r3) KL).Disjoint (reg (σ.gpr .r4) PB)
  d_kc : (reg (σ.gpr .r3) KL).Disjoint (reg (σ.gpr .r5) 1024)
  d_pc : (reg (σ.gpr .r4) PB).Disjoint (reg (σ.gpr .r5) 1024)
  b_k : (below σ.sp K).Disjoint (reg (σ.gpr .r3) KL)
  b_p : (below σ.sp K).Disjoint (reg (σ.gpr .r4) PB)
  b_c : (below σ.sp K).Disjoint (reg (σ.gpr .r5) 1024)
  f_k : (σ.gpr .r3).toNat + KL ≤ 2 ^ 64
  f_p : (σ.gpr .r4).toNat + PB ≤ 2 ^ 64
  f_c : (σ.gpr .r5).toNat + 1024 ≤ 2 ^ 64

/-- After the key's copy and the first `i` polynomials, from the entry state `σ`. -/
structure PI (KL PB K : Nat) (vals : State → Nat → Poly) (σ : State) (i : Nat) (s : State) : Prop where
  pre : PPre KL PB K σ
  r30 : s.gpr .r30 = σ.gpr .r4
  r31 : s.gpr .r31 = σ.gpr .r5
  sp : s.sp = σ.sp - BitVec.ofNat 64 144
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  pres : ∀ r ∈ preserved, r ≠ .r30 → r ≠ .r31 → s.gpr r = σ.gpr r
  key : bytesAt s.mem (σ.gpr .r4) KL = bytesAt σ.mem (σ.gpr .r3) KL
  polys : ∀ j < i, PolyIs s.mem (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * j)) (vals σ j)

section
variable {KL PB K : Nat} {vals : State → Nat → Poly} {σ : State} {i : Nat} {s : State}

/-- The bytes below the stack pointer that a call may use, apart from the
buffers, if the contract's stack covers them and our frames. -/
theorem PI.below_sub (h : PI KL PB K vals σ i s) {d : Nat} (hd : d + 144 ≤ K) :
    Region.Sub (below s.sp d) (below σ.sp K) := by
  rw [h.sp]
  have := h.pre.stk; have := σ.sp.isLt
  intro x hx
  simp only [Region.Contains] at hx ⊢
  bv_omega

/-- What a part that writes only regions apart from the key's copy and the
polynomials done keeps. -/
theorem PI.keep (h : PI KL PB K vals σ i s) {rs : List Region} {s' : State} (hk : Proof.MlKem.PPC64LE.Kept rs s s')
    (hd : ∀ r ∈ rs, (reg (σ.gpr .r4) (KL + 1024 * i)).Disjoint r) (hi : KL + 1024 * i ≤ PB) :
    PI KL PB K vals σ i s' := by
  have fp := h.pre.f_p
  refine ⟨h.pre, by rw [hk.cs .r30 (by decide), h.r30], by rw [hk.cs .r31 (by decide), h.r31],
    by rw [hk.sp, h.sp], by rw [hk.rd, h.rd], by rw [hk.wr, h.wr],
    fun r hr a b => by rw [hk.cs r hr, h.pres r hr a b], ?_, fun j hj => ?_⟩
  · have hs : Region.Sub (reg (σ.gpr .r4) KL) (reg (σ.gpr .r4) (KL + 1024 * i)) := by
      have := Offset.sub_base (σ.gpr .r4) (d := 0) (n := KL) (k := KL + 1024 * i) (by omega)
      rwa [BitVec.add_zero] at this
    rw [Proof.MlKem.bytesAt_frame hk.frame (fun r hr => (hd r hr).sub_left hs) (by omega)]
    exact h.key
  · have hs : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * j)))
        (reg (σ.gpr .r4) (KL + 1024 * i)) := Offset.sub_base _ (by omega)
    exact Proof.MlDsa.Verify.polyIs_frame hk.frame (fun r hr => (hd r hr).sub_left hs) (h.polys j hj)

end

/-! ## A polynomial -/

section
variable {KL PB K : Nat} {vals : State → Nat → Poly} {σ : State} {i : Nat} {s : State}

theorem slot_disj (P : Addr) {q : Nat} (hq : q + 1024 ≤ 2 ^ 64) :
    (reg P q).Disjoint (reg (P + BitVec.ofNat 64 q) 1024) :=
  (Offset.disjoint_base P (Nat.le_refl q) hq).symm

theorem sdepth_ntt : sdepth Impl.MlDsa.PPC64LE.Arith.ntt ≤ 96 := by decide +kernel
theorem sdepth_bitUnpack : sdepth Impl.MlDsa.PPC64LE.Pack.bitUnpack = 0 := by decide +kernel
theorem sdepth_unpackT1 : sdepth Impl.MlDsa.PPC64LE.Pack.unpackT1 = 0 := by decide +kernel

/-- The `NTT` of polynomial `i`, in its slot. -/
theorem transform_ok (h : PI KL PB K vals σ i s) (hK : 240 ≤ K) (hi : KL + 1024 * i + 1024 ≤ PB)
    (hq31 : KL + 1024 * i < 2 ^ 31) {f : Poly}
    (hf : PolyIs s.mem (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) f) (hv : vals σ i = ntt f) :
    WP isa (transform (KL + 1024 * i)) s (PI KL PB K vals σ (i + 1)) := by
  have hp := h.pre
  have fp := hp.f_p; have fc := hp.f_c
  have wP : reg (σ.gpr .r4) PB ∈ s.wr := by rw [h.wr, hp.wr]; simp
  have wC : reg (σ.gpr .r5) 1024 ∈ s.wr := by rw [h.wr, hp.wr]; simp
  have hsp : 96 ≤ s.sp.toNat := by rw [h.sp]; have := hp.stk; have := σ.sp.isLt; bv_omega
  have b96 := h.below_sub (d := 96) (by omega)
  obtain ⟨pre, c1, c2⟩ := nt_pre' (q := KL + 1024 * i) h.r30 h.r31 wP wC hp.d_pc fp fc hi hq31 hsp
    (hp.b_p.sub_left b96) (hp.b_c.sub_left b96) hf.1
  refine callV Arith.Ntt.verified.1 (by have := sdepth_ntt; omega) (ntAs_hg hq31) pre c1 c2 fun s' hk hpo => ?_
  have hd : ∀ r ∈ [reg (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) 1024, reg (σ.gpr .r5) 1024] ++
      [below s.sp (sdepth Impl.MlDsa.PPC64LE.Arith.ntt)], (reg (σ.gpr .r4) (KL + 1024 * i)).Disjoint r := by
    intro r hr
    have sP : Region.Sub (reg (σ.gpr .r4) (KL + 1024 * i)) (reg (σ.gpr .r4) PB) := by
      have := Offset.sub_base (σ.gpr .r4) (d := 0) (n := KL + 1024 * i) (k := PB) (by omega)
      rwa [BitVec.add_zero] at this
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact slot_disj _ (by omega)
    · exact hp.d_pc.sub_left sP
    · exact (hp.b_p.sub_left ((h.below_sub (d := sdepth Impl.MlDsa.PPC64LE.Arith.ntt)
        (by have := sdepth_ntt; omega)))).symm.sub_left sP
  have k := h.keep hk hd (by omega)
  refine ⟨k.pre, k.r30, k.r31, k.sp, k.rd, k.wr, k.pres, k.key, fun j hj => ?_⟩
  rcases (by omega : j < i ∨ j = i) with hj | rfl
  · exact k.polys j hj
  · have := nt_post' h.r30 hq31 hpo
    rw [hf.2, ← hv] at this
    exact this

end

/-! ## The values -/

theorem secret_val (p : Params) (sk : List Byte) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    ntt (toRq (bitUnpack ((sk.drop (secretPiece p i).1).take (secretPiece p i).2.1) (secretPiece p i).2.2.1
      (secretPiece p i).2.2.2)) = (preparedSecretPolys p sk)[i]! := by
  unfold secretPiece
  split
  · rcases (by omega : i < p.ℓ ∨ p.ℓ ≤ i) with h | h
    · rw [Proof.MlDsa.PreparedKey.secret_s1 p sk h]; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, i = p.ℓ + j := ⟨i - p.ℓ, by omega⟩
      rw [Proof.MlDsa.PreparedKey.secret_s2 p sk (by omega)]
      simp only [Proof.MlDsa.Sign.s2F, Proof.MlDsa.Sign.lenS, secretLen, Nat.mul_add, Nat.add_assoc]
  · obtain ⟨j, rfl⟩ : ∃ j, i = p.ℓ + p.k + j := ⟨i - p.ℓ - p.k, by omega⟩
    rw [Proof.MlDsa.PreparedKey.secret_t0 p sk (by omega)]
    simp only [Proof.MlDsa.Sign.t0F, Proof.MlDsa.Sign.lenS, secretLen, Nat.mul_add, Nat.add_assoc,
      Nat.add_sub_cancel_left]
    rfl

theorem public_val (p : Params) (pk : List Byte) {i : Nat} (hi : i < p.k) :
    ntt ((simpleBitUnpack ((pk.drop (32 + 320 * i)).take 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) =
      (preparedPublicPolys p pk)[i]! := by
  rw [Proof.MlDsa.PreparedKey.public_poly p pk hi]; rfl

theorem secret_args {p : Params} (hF : Sign.SFacts p) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    BuArgs (preparedSecretKeyBytes p) (secretPiece p i).1 (secretPiece p i).2.1 (secretPiece p i).2.2.1
      (secretPiece p i).2.2.2 (p.skLen + 1024 * i) ∧ (secretPiece p i).1 + (secretPiece p i).2.1 ≤ p.skLen := by
  have hk := hF.k; have hl := hF.l; have hsk := hF.sk; have hlens := hF.lens
  have hPB : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k) := by
    show _ + 4 * 256 * _ = _; omega
  have hab : (p.η, p.η) ∈ bitPackParams ∧ secretLen p = 32 * bitlen (p.η + p.η) ∧ 0 < secretLen p ∧
      secretLen p < 2 ^ 31 ∧ p.η < 2 ^ 31 := by
    refine ⟨?_, by rw [← Nat.two_mul], ?_⟩
    · rcases hF.eta with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> decide
    · rcases hF.eta with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [show secretLen p = Impl.MlDsa.PPC64LE.Sign.sLen p from rfl, l, e] <;>
        decide
  have hsl : secretLen p = Impl.MlDsa.PPC64LE.Sign.sLen p := rfl
  unfold secretPiece
  split
  · have hm : secretLen p * (i + 1) ≤ secretLen p * (p.ℓ + p.k) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    dsimp only
    refine ⟨⟨?_, ?_, hab.1, hab.2.1, hab.2.2.1, hab.2.2.2.1, hab.2.2.2.2, hab.2.2.2.2, ?_⟩, ?_⟩ <;>
      (try rw [hsl] at *) <;> omega
  · dsimp only
    refine ⟨⟨?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩, ?_⟩ <;>
      (try rw [hsl] at *) <;> omega

/-! ## The steps -/

/-- The polynomials of a prepared private key, of the key at entry. -/
abbrev svals (p : Params) (σ : State) (j : Nat) : Poly :=
  (preparedSecretPolys p (bytesAt σ.mem (σ.gpr .r3) p.skLen))[j]!

/-- The polynomials of a prepared public key, of the key at entry. -/
abbrev pvals (p : Params) (σ : State) (j : Nat) : Poly :=
  (preparedPublicPolys p (bytesAt σ.mem (σ.gpr .r3) p.pkLen))[j]!

theorem slot_keep {P : Addr} {KL i PB : Nat} {sp : Addr} (hi : KL + 1024 * i + 1024 ≤ PB) (hf : P.toNat + PB ≤ 2 ^ 64) :
    ∀ r ∈ [reg (P + BitVec.ofNat 64 (KL + 1024 * i)) 1024] ++ [below sp 0], (reg P (KL + 1024 * i)).Disjoint r := by
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact slot_disj _ (by omega)
  · exact (below0 _ _).symm

/-! ## The setup and the result -/

theorem sp144 (sp : Addr) : sp - 48 - 48 - 48 = sp - BitVec.ofNat 64 144 := by bv_omega

/-- `d ← n`. -/
abbrev mv (d n : Reg) (s : State) : State := s.write d (s.gpr n + BitVec.ofNat 64 0)

/-- The state after the moves of the pointers and the copy's arguments. -/
abbrev movSt (KL : Nat) (s : State) : State := (mv .r9 .r4 (mv .r31 .r5 (mv .r30 .r4 s))).write .r5 (BitVec.ofNat 64 (KL / 8))

/-- The moves of the frames' body. -/
abbrev movs (KL : Nat) : List Instr :=
  [Impl.Sha3.PPC64LE.Stream.mov .r30 .r4, Impl.Sha3.PPC64LE.Stream.mov .r31 .r5,
    Impl.Sha3.PPC64LE.Stream.mov .r9 .r4, .li .r5 (KL / 8)]

theorem movs_ok {KL : Nat} (hc : KL / 8 < 2 ^ 15) (s : State) : WP isa (.block (movs KL)) s (· = movSt KL s) :=
  WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_addi (by decide) (by decide))
    (WP.cons (exec_addi (by decide) (by decide)) (WP.cons (exec_li hc) (WP.block_nil rfl))))

theorem movSt_gpr {KL : Nat} (σ : State) :
    (movSt KL (f3St σ)).gpr .r3 = σ.gpr .r3 ∧ (movSt KL (f3St σ)).gpr .r9 = σ.gpr .r4 ∧
    (movSt KL (f3St σ)).gpr .r5 = BitVec.ofNat 64 (KL / 8) ∧ (movSt KL (f3St σ)).gpr .r30 = σ.gpr .r4 ∧
    (movSt KL (f3St σ)).gpr .r31 = σ.gpr .r5 := by
  simp only [movSt, mv, RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.add_zero]
  exact ⟨f3St_gpr σ (by decide), f3St_gpr σ (by decide), trivial, f3St_gpr σ (by decide), f3St_gpr σ (by decide)⟩

/-- The encoded key copied to `prepared`. -/
theorem copy_ok {KL PB K : Nat} {vals : State → Nat → Poly} {σ : State} (hp : PPre KL PB K σ) (hK : 240 ≤ K)
    (hKL : KL % 8 = 0) (h8 : 8 ≤ KL) (hc : KL / 8 < 2 ^ 15) (hPB : KL ≤ PB) :
    WP isa Impl.Gather.PPC64LE.copyWords (movSt KL (f3St σ)) (PI KL PB K vals σ 0) := by
  have fk := hp.f_k; have fpp := hp.f_p
  have e8 : 8 * (KL / 8) = KL := by omega
  obtain ⟨g3, g9, g5, g30, g31⟩ := movSt_gpr (KL := KL) σ
  have g : ∀ r, r ≠ .r0 → (f3St σ).gpr r = σ.gpr r := fun r h => f3St_gpr σ h
  have sK : Region.Sub (reg (σ.gpr .r4) KL) (reg (σ.gpr .r4) PB) := by
    have := Offset.sub_base (σ.gpr .r4) (d := 0) (n := KL) (k := PB) (by omega)
    rwa [BitVec.add_zero] at this
  refine WP.mono (Gather.PPC64LE.copyWords_wp _ (S := σ.gpr .r3) (D := σ.gpr .r4) (k := KL / 8)
    ⟨g3, g9, g5, by omega, by omega, ?_, ?_, ?_⟩) fun s' ⟨hm, _, _, _, kp⟩ => ?_
  · rw [e8]
    show Covers [reg (σ.gpr .r3) KL] (σ.rd ++ σ.wr)
    rw [hp.rd]; exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨reg (σ.gpr .r3) KL, by simp, 0, by simp, by simp⟩
  · rw [e8]
    show Covers [reg (σ.gpr .r4) KL] σ.wr
    rw [hp.wr]; exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨reg (σ.gpr .r4) PB, by simp, 0, by simp, by simpa using hPB⟩
  · rw [e8]; exact hp.d_kp.sub_right sK
  simp only [RegUpd.mem_write] at hm
  have b144 : Region.Sub (below σ.sp 144) (below σ.sp K) :=
    below_sub (by omega) (by have := hp.stk; have := σ.sp.isLt; omega)
  refine ⟨hp, ?_, ?_, ?_, kp.rd, kp.wr, fun r hr a b => ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [kp.gpr _ (by decide), g30]
  · rw [kp.gpr _ (by decide), g31]
  · rw [kp.sp]; exact sp144 σ.sp
  · have : r ∉ ([.r0, .r3, .r4, .r5, .r6, .r9] : List Reg) ∧ r ≠ .r9 ∧ r ≠ .r5 ∧ r ≠ .r0 := by
      revert r; decide
    rw [kp.gpr r this.1]
    simp only [movSt, mv, RegUpd.gpr_write, a, b, this.2.1, this.2.2.1, ite_false]
    exact g r this.2.2.2
  · rw [hm]
    have hl : (Spec.Aes.bytesAt (f3St σ).mem (σ.gpr .r3) (8 * (KL / 8))).length = KL := by
      simp [Spec.Aes.bytesAt, e8]
    have := bytesAt_writeBytes_self (f3St σ).mem (σ.gpr .r4) (Spec.Aes.bytesAt (f3St σ).mem (σ.gpr .r3) (8 * (KL / 8)))
      (by rw [hl]; omega)
    rw [hl] at this
    rw [this, e8]
    exact Proof.MlKem.bytesAt_frame (f3St_mem σ (by have := hp.stk; omega)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact (hp.b_k.sub_left b144).symm) (by omega)

theorem secret_final {p : Params} {PB K : Nat} {σ s : State}
    (h : PI p.skLen PB K (svals p) σ (p.ℓ + 2 * p.k) s) :
    bytesAt s.mem (σ.gpr .r4) p.skLen = bytesAt σ.mem (σ.gpr .r3) p.skLen ∧ PreparedSecretKey p s.mem (σ.gpr .r4) :=
  ⟨h.key, fun i hi => by
    rw [h.key]
    have := h.polys i hi
    rw [show p.skLen + 1024 * i = p.skLen + 4 * n * i by show _ = _ + 4 * 256 * i; omega] at this
    exact Proof.MlDsa.polyStored_iff.mpr this⟩

theorem public_final {p : Params} {PB K : Nat} {σ s : State}
    (h : PI p.pkLen PB K (pvals p) σ p.k s) :
    bytesAt s.mem (σ.gpr .r4) p.pkLen = bytesAt σ.mem (σ.gpr .r3) p.pkLen ∧ PreparedPublicKey p s.mem (σ.gpr .r4) :=
  ⟨h.key, fun i hi => by
    rw [h.key]
    have := h.polys i hi
    rw [show p.pkLen + 1024 * i = p.pkLen + 4 * n * i by show _ = _ + 4 * 256 * i; omega] at this
    exact Proof.MlDsa.polyStored_iff.mpr this⟩

/-! ## Both runs -/

/-- What two runs share: the stack pointer and the pointers. -/
abbrev PPub (σ₁ σ₂ : State) : Prop :=
  σ₁.sp = σ₂.sp ∧ σ₁.gpr .r3 = σ₂.gpr .r3 ∧ σ₁.gpr .r4 = σ₂.gpr .r4 ∧ σ₁.gpr .r5 = σ₂.gpr .r5

/-- Polynomial `i` unpacked to its slot, before its transform. -/
def Mid (KL PB K : Nat) (vals : State → Nat → Poly) (σ : State) (i : Nat) (s : State) : Prop :=
  PI KL PB K vals σ i s ∧ ∃ f, PolyIs s.mem (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) f ∧ vals σ i = ntt f

section
variable {KL PB K : Nat} {vals : State → Nat → Poly}

theorem PI.nt {σ s : State} {i : Nat} (h : PI KL PB K vals σ i s) (hK : 240 ≤ K) (hi : KL + 1024 * i + 1024 ≤ PB)
    (hq31 : KL + 1024 * i < 2 ^ 31) (hr : Reduced s.mem (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i))) :
    (nttContract PPC64LE.abi 96).pre (KeyGen.view (glueSt s (ntAs (KL + 1024 * i))) []
      [reg (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) 1024, reg (σ.gpr .r5) 1024]) ∧
    Covers ([] ++ [reg (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) 1024, reg (σ.gpr .r5) 1024]) (s.rd ++ s.wr) ∧
    Covers [reg (σ.gpr .r4 + BitVec.ofNat 64 (KL + 1024 * i)) 1024, reg (σ.gpr .r5) 1024] s.wr := by
  have hp := h.pre
  have fp := hp.f_p; have fc := hp.f_c
  have wP : reg (σ.gpr .r4) PB ∈ s.wr := by rw [h.wr, hp.wr]; simp
  have wC : reg (σ.gpr .r5) 1024 ∈ s.wr := by rw [h.wr, hp.wr]; simp
  have hsp : 96 ≤ s.sp.toNat := by rw [h.sp]; have := hp.stk; have := σ.sp.isLt; bv_omega
  have b96 := h.below_sub (d := 96) (by omega)
  exact nt_pre' h.r30 h.r31 wP wC hp.d_pc fp fc hi hq31 hsp (hp.b_p.sub_left b96) (hp.b_c.sub_left b96) hr

theorem transform_piece (hK : 240 ≤ K) {i : Nat} (hi : KL + 1024 * i + 1024 ≤ PB) (hq31 : KL + 1024 * i < 2 ^ 31) :
    KeyGen.Piece (PPre KL PB K) PPub (fun σ s => Mid KL PB K vals σ i s)
      (fun σ s => PI KL PB K vals σ (i + 1) s) (transform (KL + 1024 * i)) where
  ok _ _ _ h := by obtain ⟨h, f, hf, hv⟩ := h; exact transform_ok h hK hi hq31 hf hv
  tr := by
    refine callV_tr Arith.Ntt.verified.1 Arith.Ntt.verified.2.1 (ntAs_hg hq31) fun x y hxy => ?_
    obtain ⟨σ₁, σ₂, -, -, ⟨e0, -, e4, e5⟩, ⟨h₁, f₁, hf₁, -⟩, ⟨h₂, f₂, hf₂, -⟩⟩ := hxy
    obtain ⟨p1, c1, c2⟩ := h₁.nt hK hi hq31 hf₁.1
    obtain ⟨p2, d1, d2⟩ := h₂.nt hK hi hq31 hf₂.1
    rw [← e4, ← e5] at p2 d1 d2
    exact ⟨_, _, p1, p2, nt_pub' hq31 (by rw [h₁.sp, h₂.sp, e0]) (by rw [h₁.r30, h₂.r30, e4])
      (by rw [h₁.r31, h₂.r31, e5]), c1, c2, d1, d2⟩

theorem movs_piece (hc : KL / 8 < 2 ^ 15) :
    KeyGen.Piece (PPre KL PB K) PPub (fun σ s => s = f3St σ) (fun σ s => s = movSt KL (f3St σ)) (.block (movs KL)) :=
  ⟨fun _ _ _ e => by subst e; exact movs_ok hc _, VG.Proof.Sha3.PPC64LE.Pieces.relct_noMem rfl⟩

theorem copy_piece (hK : 240 ≤ K) (hKL : KL % 8 = 0) (h8 : 8 ≤ KL) (hc : KL / 8 < 2 ^ 15) (hPB : KL ≤ PB) :
    KeyGen.Piece (PPre KL PB K) PPub (fun σ s => s = movSt KL (f3St σ)) (fun σ s => PI KL PB K vals σ 0 s)
      Impl.Gather.PPC64LE.copyWords := by
  refine ⟨fun σ _ hp e => by subst e; exact copy_ok hp hK hKL h8 hc hPB, ?_⟩
  refine RelCT.taint (A := VG.PPC64LE.taint) (Taint.ofRegs [.r3, .r5, .r9])
    (fun a b ⟨σ₁, σ₂, _, _, ⟨e0, e3, e4, _⟩, ea, eb⟩ => ?_) (by taint_decide)
  subst ea eb
  obtain ⟨x3, x9, x5, -⟩ := movSt_gpr (KL := KL) σ₁
  obtain ⟨y3, y9, y5, -⟩ := movSt_gpr (KL := KL) σ₂
  refine ⟨by show (f3St σ₁).sp = (f3St σ₂).sp; rw [f3St_sp, f3St_sp, e0], fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [x3, y3, e3]
  · rw [x5, y5]
  · rw [x9, y9, e4]

/-- The frames' body, from the polynomials' pieces. -/
theorem body_piece (hK : 240 ≤ K) (hKL : KL % 8 = 0) (h8 : 8 ≤ KL) (hc : KL / 8 < 2 ^ 15) (hPB : KL ≤ PB)
    {f : Nat → Prog isa} {n : Nat}
    (hf : ∀ i < n, KeyGen.Piece (PPre KL PB K) PPub (fun σ s => PI KL PB K vals σ i s)
      (fun σ s => PI KL PB K vals σ (i + 1) s) (f i)) :
    KeyGen.Piece (PPre KL PB K) PPub (fun σ s => s = f3St σ) (fun σ s => PI KL PB K vals σ n s)
      (.seq (.block (movs KL)) (.seq Impl.Gather.PPC64LE.copyWords (seqR f 0 n))) := by
  have hl := KeyGen.Piece.seqR (Pre := PPre KL PB K) (Pub := PPub) (I := fun i σ s => PI KL PB K vals σ i s) n 0
    fun k _ hk => hf k (by omega)
  rw [Nat.zero_add] at hl
  exact (movs_piece hc).seq ((copy_piece hK hKL h8 hc hPB).seq hl)

/-- The frames around the body: its memory, and the registers kept. -/
theorem frames_wp {n : Nat} {body : Prog isa}
    (hP : KeyGen.Piece (PPre KL PB K) PPub (fun σ s => s = f3St σ) (fun σ s => PI KL PB K vals σ n s) body)
    (hK : 144 ≤ K) (hn : sdepth body + 144 < 2 ^ 64) {σ : State} (hp : PPre KL PB K σ) :
    WP isa (frames3 body) σ fun s' => PPC64LE.target.abiPreserved σ s' ∧
      ∃ s, PI KL PB K vals σ n s ∧ s.mem = s'.mem := by
  have hs := hp.stk
  have b144 : Region.Sub (below σ.sp 144) (below σ.sp K) := below_sub (by omega) (by have := σ.sp.isLt; omega)
  refine frames3_wp (R := fun m => ∃ s, PI KL PB K vals σ n s ∧ s.mem = m) (by omega) (fun X hX => ?_) hn
    (WP.mono (hP.ok σ _ hp rfl) fun s' h => ⟨h.pres, s', h, rfl⟩)
  rw [hp.wr] at hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · exact hp.b_p.sub_left b144
  · exact hp.b_c.sub_left b144

theorem frames_tr {n : Nat} {body : Prog isa}
    (hP : KeyGen.Piece (PPre KL PB K) PPub (fun σ s => s = f3St σ) (fun σ s => PI KL PB K vals σ n s) body)
    (hK : 144 ≤ K) (hn : sdepth body + 144 < 2 ^ 64) :
    RelCT isa (fun x y => PPre KL PB K x ∧ PPre KL PB K y ∧ PPub x y) (frames3 body) fun _ _ => True := by
  refine frames3_tr (fun x y h => h.2.2.1) (fun x hx => ?_) hn
    (RelCT.mono hP.tr (fun u v ⟨x, y, ⟨a, b, c⟩, eu, ev⟩ => ⟨x, y, a, b, c, eu, ev⟩) fun _ _ h => h)
  have hp : PPre KL PB K x := by
    obtain ⟨y, h | h⟩ := hx
    · exact h.1
    · exact h.2.1
  have hs := hp.stk
  have b144 : Region.Sub (below x.sp 144) (below x.sp K) := below_sub (by omega) (by have := x.sp.isLt; omega)
  refine ⟨by omega, fun X hX => ?_, _, hP.ok x _ hp rfl⟩
  rw [hp.wr] at hX
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl
  · exact hp.b_p.sub_left b144
  · exact hp.b_c.sub_left b144

end

/-! ## The polynomials -/

section
variable {p : Params} {K : Nat}

theorem secret_unpack (hF : Sign.SFacts p) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    KeyGen.Piece (PPre p.skLen (preparedSecretKeyBytes p) K) PPub
      (fun σ s => PI p.skLen (preparedSecretKeyBytes p) K (svals p) σ i s)
      (fun σ s => Mid p.skLen (preparedSecretKeyBytes p) K (svals p) σ i s)
      (callAt "vg_mldsa_bit_unpack" Impl.MlDsa.PPC64LE.Pack.bitUnpack (buAs (secretPiece p i).1 (secretPiece p i).2.1
        (secretPiece p i).2.2.1 (secretPiece p i).2.2.2 (p.skLen + 1024 * i))) := by
  obtain ⟨m, hle⟩ := secret_args hF hi
  have hlens := hF.lens; have hk := hF.k; have hl := hF.l
  have hPB : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k) := by
    show _ + 4 * 256 * _ = _; omega
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · have hp := h.pre
    have fp := hp.f_p
    have wP : reg (σ.gpr .r4) (preparedSecretKeyBytes p) ∈ s.wr := by rw [h.wr, hp.wr]; simp
    obtain ⟨pre, c1, c2⟩ := bu_pre' h.r30 wP fp m
    refine callV Pack.bitUnpack_verified.1 (by rw [sdepth_bitUnpack]; decide) m.hg pre c1 c2 fun s₁ hk hpo => ?_
    rw [sdepth_bitUnpack] at hk
    refine ⟨h.keep hk (slot_keep (by omega) fp) (by omega), _, bu_post' h.r30 m hpo, ?_⟩
    rw [← Proof.MlKem.bytesAt_slice _ _ hle, h.key]
    exact (secret_val p _ hi).symm
  · refine callV_tr Pack.bitUnpack_verified.1 Pack.bitUnpack_verified.2.1 m.hg fun x y hxy => ?_
    obtain ⟨σ₁, σ₂, -, -, ⟨e0, -, e4, -⟩, h₁, h₂⟩ := hxy
    have w1 : reg (σ₁.gpr .r4) (preparedSecretKeyBytes p) ∈ x.wr := by rw [h₁.wr, h₁.pre.wr]; simp
    have w2 : reg (σ₂.gpr .r4) (preparedSecretKeyBytes p) ∈ y.wr := by rw [h₂.wr, h₂.pre.wr]; simp
    obtain ⟨p1, c1, c2⟩ := bu_pre' h₁.r30 w1 h₁.pre.f_p m
    obtain ⟨p2, d1, d2⟩ := bu_pre' h₂.r30 w2 h₂.pre.f_p m
    rw [← e4] at p2 d1 d2
    exact ⟨_, _, p1, p2, bu_pub' m (by rw [h₁.sp, h₂.sp, e0]) (by rw [h₁.r30, h₂.r30, e4]), c1, c2, d1, d2⟩

theorem secret_piece (hF : Sign.SFacts p) (hK : 240 ≤ K) {i : Nat} (hi : i < p.ℓ + 2 * p.k) :
    KeyGen.Piece (PPre p.skLen (preparedSecretKeyBytes p) K) PPub
      (fun σ s => PI p.skLen (preparedSecretKeyBytes p) K (svals p) σ i s)
      (fun σ s => PI p.skLen (preparedSecretKeyBytes p) K (svals p) σ (i + 1) s) (secretPoly p i) := by
  have hlens := hF.lens; have hk := hF.k; have hl := hF.l
  have hPB : preparedSecretKeyBytes p = p.skLen + 1024 * (p.ℓ + 2 * p.k) := by
    show _ + 4 * 256 * _ = _; omega
  exact (secret_unpack hF hi).seq (transform_piece hK (by omega) (by omega))

theorem public_unpack (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {i : Nat} (hi : i < p.k) :
    KeyGen.Piece (PPre p.pkLen (preparedPublicKeyBytes p) K) PPub
      (fun σ s => PI p.pkLen (preparedPublicKeyBytes p) K (pvals p) σ i s)
      (fun σ s => Mid p.pkLen (preparedPublicKeyBytes p) K (pvals p) σ i s)
      (callAt "vg_mldsa_unpack_t1" Impl.MlDsa.PPC64LE.Pack.unpackT1 (t1As (32 + 320 * i) (p.pkLen + 1024 * i))) := by
  have hpk : p.pkLen = 32 + 320 * p.k ∧ p.k ≤ 8 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hPB : preparedPublicKeyBytes p = p.pkLen + 1024 * p.k := by
    show _ + 4 * 256 * _ = _; omega
  have m : T1Args (preparedPublicKeyBytes p) (32 + 320 * i) (p.pkLen + 1024 * i) := ⟨by omega, by omega, by omega⟩
  refine ⟨fun σ s _ h => ?_, ?_⟩
  · have hp := h.pre
    have fp := hp.f_p
    have wP : reg (σ.gpr .r4) (preparedPublicKeyBytes p) ∈ s.wr := by rw [h.wr, hp.wr]; simp
    obtain ⟨pre, c1, c2⟩ := t1_pre' h.r30 wP fp m
    refine callV Pack.unpackT1_verified.1 (by rw [sdepth_unpackT1]; decide) m.hg pre c1 c2 fun s₁ hk hpo => ?_
    rw [sdepth_unpackT1] at hk
    refine ⟨h.keep hk (slot_keep (by omega) fp) (by omega), _, t1_post' h.r30 m hpo, ?_⟩
    rw [← Proof.MlKem.bytesAt_slice _ _ (show 32 + 320 * i + 320 ≤ p.pkLen by omega), h.key]
    exact (public_val p _ hi).symm
  · refine callV_tr Pack.unpackT1_verified.1 Pack.unpackT1_verified.2.1 m.hg fun x y hxy => ?_
    obtain ⟨σ₁, σ₂, -, -, ⟨e0, -, e4, -⟩, h₁, h₂⟩ := hxy
    have w1 : reg (σ₁.gpr .r4) (preparedPublicKeyBytes p) ∈ x.wr := by rw [h₁.wr, h₁.pre.wr]; simp
    have w2 : reg (σ₂.gpr .r4) (preparedPublicKeyBytes p) ∈ y.wr := by rw [h₂.wr, h₂.pre.wr]; simp
    obtain ⟨p1, c1, c2⟩ := t1_pre' h₁.r30 w1 h₁.pre.f_p m
    obtain ⟨p2, d1, d2⟩ := t1_pre' h₂.r30 w2 h₂.pre.f_p m
    rw [← e4] at p2 d1 d2
    exact ⟨_, _, p1, p2, t1_pub' m (by rw [h₁.sp, h₂.sp, e0]) (by rw [h₁.r30, h₂.r30, e4]), c1, c2, d1, d2⟩

theorem public_piece (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (hK : 240 ≤ K) {i : Nat} (hi : i < p.k) :
    KeyGen.Piece (PPre p.pkLen (preparedPublicKeyBytes p) K) PPub
      (fun σ s => PI p.pkLen (preparedPublicKeyBytes p) K (pvals p) σ i s)
      (fun σ s => PI p.pkLen (preparedPublicKeyBytes p) K (pvals p) σ (i + 1) s) (publicPoly p i) := by
  have hpk : p.pkLen = 32 + 320 * p.k ∧ p.k ≤ 8 := by rcases hp3 with rfl | rfl | rfl <;> decide
  have hPB : preparedPublicKeyBytes p = p.pkLen + 1024 * p.k := by
    show _ + 4 * 256 * _ = _; omega
  exact (public_unpack hp3 hi).seq (transform_piece hK (by omega) (by omega))

end

/-! ## The functions -/

theorem sdepth_copyWords : sdepth Impl.Gather.PPC64LE.copyWords = 0 := by decide +kernel

theorem sdepth_seqR {f : Nat → Prog isa} {B : Nat} (h : ∀ k, sdepth (f k) ≤ B) :
    ∀ n a, sdepth (seqR f a n) ≤ B
  | 0, _ => Nat.zero_le _
  | n + 1, a => by
    simp only [seqR, sdepth]
    exact Nat.max_le.mpr ⟨h a, sdepth_seqR h n (a + 1)⟩

theorem sdepth_body {KL : Nat} {f : Nat → Prog isa} (hf : ∀ i, sdepth (f i) ≤ 96) (n : Nat) :
    sdepth (.seq (.block (movs KL)) (.seq Impl.Gather.PPC64LE.copyWords (seqR f 0 n)) : Prog isa) ≤ 96 := by
  simp only [sdepth, sdepth_copyWords, Nat.zero_max]
  exact sdepth_seqR hf n 0

theorem sdepth_secretPoly (p : Params) (i : Nat) : sdepth (secretPoly p i) ≤ 96 := by
  simp only [secretPoly, transform, callAt, sdepth, sdepth_bitUnpack, Nat.zero_max]
  exact sdepth_ntt

theorem sdepth_publicPoly (p : Params) (i : Nat) : sdepth (publicPoly p i) ≤ 96 := by
  simp only [publicPoly, transform, callAt, sdepth, sdepth_unpackT1, Nat.zero_max]
  exact sdepth_ntt

/-- A state meeting a preparation's precondition. -/
def prepSat (bytes count : Nat) : State where
  gpr r := match r with | .r3 => 0x1000 | .r4 => 0x10000 | .r5 => 0x100000 | _ => 0
  lr := 0
  sp := 0x1000000
  mem _ := 0
  rd := [⟨0x1000, bytes⟩]
  wr := [⟨0x10000, bytes + 1024 * count⟩, ⟨0x100000, 1024⟩]

theorem secret_pre {p : Params} {σ : State} (h : (prepareSecretKeyContract p PPC64LE.abi 240).pre σ) :
    PPre p.skLen (preparedSecretKeyBytes p) 240 σ := by
  sig_pre [prepareSecretKeyContract, prepareSecretKeySig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem public_pre {p : Params} {σ : State} (h : (preparePublicKeyContract p PPC64LE.abi 240).pre σ) :
    PPre p.pkLen (preparedPublicKeyBytes p) 240 σ := by
  sig_pre [preparePublicKeyContract, preparePublicKeySig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

section
variable {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include hp3

theorem secret_body : KeyGen.Piece (PPre p.skLen (preparedSecretKeyBytes p) 240) PPub (fun σ s => s = f3St σ)
    (fun σ s => PI p.skLen (preparedSecretKeyBytes p) 240 (svals p) σ (p.ℓ + 2 * p.k) s)
    (.seq (.block (movs p.skLen)) (.seq Impl.Gather.PPC64LE.copyWords (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k)))) := by
  have hF := Sign.sfacts hp3
  have h : p.skLen % 8 = 0 ∧ 8 ≤ p.skLen ∧ p.skLen / 8 < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  exact body_piece (by decide) h.1 h.2.1 h.2.2 (by simp only [preparedSecretKeyBytes]; omega)
    fun i hi => secret_piece hF (by decide) hi

theorem public_body : KeyGen.Piece (PPre p.pkLen (preparedPublicKeyBytes p) 240) PPub (fun σ s => s = f3St σ)
    (fun σ s => PI p.pkLen (preparedPublicKeyBytes p) 240 (pvals p) σ p.k s)
    (.seq (.block (movs p.pkLen)) (.seq Impl.Gather.PPC64LE.copyWords (seqR (publicPoly p) 0 p.k))) := by
  have h : p.pkLen % 8 = 0 ∧ 8 ≤ p.pkLen ∧ p.pkLen / 8 < 2 ^ 15 := by rcases hp3 with rfl | rfl | rfl <;> decide
  exact body_piece (by decide) h.1 h.2.1 h.2.2 (by simp only [preparedPublicKeyBytes]; omega)
    fun i hi => public_piece hp3 (by decide) hi

theorem secret_sat : (prepareSecretKeyContract p PPC64LE.abi 240).pre (prepSat p.skLen (p.ℓ + 2 * p.k)) := by
  rcases hp3 with rfl | rfl | rfl
  all_goals sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, PPC64LE.abi, PPC64LE.argRegs, prepSat]

theorem public_sat : (preparePublicKeyContract p PPC64LE.abi 240).pre (prepSat p.pkLen p.k) := by
  rcases hp3 with rfl | rfl | rfl
  all_goals sig_sat_check [preparePublicKeyContract, preparePublicKeySig, PPC64LE.abi, PPC64LE.argRegs, prepSat]

theorem prepareSecret_verified :
    Verified PPC64LE.target (prepareSecret p) (prepareSecretKeyContract p PPC64LE.abi 240) := by
  have hn := sdepth_body (KL := p.skLen) (sdepth_secretPoly p) (p.ℓ + 2 * p.k)
  refine ⟨fun σ hs => ?_, fun x y tx ty x' y' hx hy hpub ex ey => ?_, ?_⟩
  · refine WP.mono (frames_wp (secret_body hp3) (by decide) (by omega) (secret_pre hs))
      fun s' ⟨ha, s, h, hm⟩ => ⟨ha, ?_⟩
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, PPC64LE.abi, PPC64LE.argRegs]
    rw [← hm]
    exact secret_final h
  · sig_pub [prepareSecretKeyContract, prepareSecretKeySig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    exact (frames_tr (secret_body hp3) (by decide) (by omega) _ _ _ _ _ _
      ⟨secret_pre hx, secret_pre hy, hpub.1, hpub.2.1, hpub.2.2.1, hpub.2.2.2⟩ ex ey).1
  · exact ⟨_, secret_sat hp3⟩

theorem preparePublic_verified :
    Verified PPC64LE.target (preparePublic p) (preparePublicKeyContract p PPC64LE.abi 240) := by
  have hn := sdepth_body (KL := p.pkLen) (sdepth_publicPoly p) p.k
  refine ⟨fun σ hs => ?_, fun x y tx ty x' y' hx hy hpub ex ey => ?_, ?_⟩
  · refine WP.mono (frames_wp (public_body hp3) (by decide) (by omega) (public_pre hs))
      fun s' ⟨ha, s, h, hm⟩ => ⟨ha, ?_⟩
    sig_post [preparePublicKeyContract, preparePublicKeySig, PPC64LE.abi, PPC64LE.argRegs]
    rw [← hm]
    exact public_final h
  · sig_pub [preparePublicKeyContract, preparePublicKeySig, PPC64LE.abi, PPC64LE.argRegs] at hpub
    exact (frames_tr (public_body hp3) (by decide) (by omega) _ _ _ _ _ _
      ⟨public_pre hx, public_pre hy, hpub.1, hpub.2.1, hpub.2.2.1, hpub.2.2.2⟩ ex ey).1
  · exact ⟨_, public_sat hp3⟩

end

/-! ## Memory with a prepared key -/

section
variable {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
include hp3

/-- Some memory holds a prepared private key at `0x10000`: what the
preparation writes, from `prepSat`. -/
theorem secret_mem : ∃ m : Mem, PreparedSecretKey p m 0x10000 := by
  obtain ⟨_, s', -, -, hq⟩ := (prepareSecret_verified hp3).1 _ (secret_sat hp3)
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, PPC64LE.abi, PPC64LE.argRegs] at hq
  exact ⟨s'.mem, hq.2⟩

/-- Some memory holds a prepared public key at `0x10000`. -/
theorem public_mem : ∃ m : Mem, PreparedPublicKey p m 0x10000 := by
  obtain ⟨_, s', -, -, hq⟩ := (preparePublic_verified hp3).1 _ (public_sat hp3)
  sig_post [preparePublicKeyContract, preparePublicKeySig, PPC64LE.abi, PPC64LE.argRegs] at hq
  exact ⟨s'.mem, hq.2⟩

end

end VG.Proof.MlDsa.PPC64LE.PreparedKey
