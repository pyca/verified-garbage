import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.X86.Compress
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Gb`. -/
section

section

/-!
# Argon2 on x86 (32-bit): the steps of GB

Each step of GB (`VG.Impl.Argon2.X86.gb`) reads its operands from `scratch`
(at `esi`) and writes its result back. `addMul_ok`, `xorRot32_ok`, `xorRot_ok`
and `xorRot63_ok` give the memory each leaves, for any offsets, with the
64-bit operations on register pairs of `Proof/Sha512/X86/Rounds.lean` and
the rotations of `Proof/Blake2/X86/CompressB/G.lean`.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86
open VG.Impl.Argon2.X86 (addMul xor64m xorLd xorRot32 xorRot xorRot63)
open VG.Impl.Sha512.X86 (ld st add64 add64m)
open VG.Proof.Sha512.X86 (Only Pair Acc rd64 write64 wp_ld wp_st wp_add64 wp_add64m wp_xorS
  wp_movS mem_rd readSrc_mem lo_rd64 hi_rd64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_toNat hi_toNat)
open VG.Proof.Sha256.X86.Stream (Upd Mupd)
open VG.Proof.Blake2.X86.CompressB (wp_rot wp_rot')

/-! ## States -/

/-- The registers GB writes. -/
def temps : List Reg := [.eax, .ecx, .edx]

/-- `s'` is `s` but for the registers GB writes, the flags and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.Argon2.X86.temps → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : VG.Proof.Argon2.X86.Keep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : VG.Proof.Argon2.X86.Keep s s₁) (k₂ : VG.Proof.Argon2.X86.Keep s₁ s₂) : VG.Proof.Argon2.X86.Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr⟩

theorem Keep.of_only {s s' : State} {ds : List Reg} (o : Only ds s s') (h : ∀ r ∈ ds, r ∈ VG.Proof.Argon2.X86.temps) :
    VG.Proof.Argon2.X86.Keep s s' :=
  ⟨fun r hr => o.gpr r fun hd => hr (h r hd), o.rd, o.wr⟩

theorem Keep.of_wrote {s s₁ s₂ : State} {ds : List Reg} {m : Mem} (o : Only ds s s₁)
    (u : Mupd s₁ s₂ m) (h : ∀ r ∈ ds, r ∈ VG.Proof.Argon2.X86.temps) : VG.Proof.Argon2.X86.Keep s s₂ :=
  ⟨fun r hr => by rw [u.gpr]; exact o.gpr r fun hd => hr (h r hd), u.rd.trans o.rd,
    u.wr.trans o.wr⟩

theorem Keep.esi {s s' : State} (k : VG.Proof.Argon2.X86.Keep s s') : s'.gpr .esi = s.gpr .esi := k.gpr _ (by decide)

/-! ## `mul` -/

theorem lo_ofNat (p : Nat) : lo (BitVec.ofNat 64 p) = BitVec.ofNat 32 p := by
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]

theorem hi_ofNat {p : Nat} (h : p < 2 ^ 64) : hi (BitVec.ofNat 64 p) = BitVec.ofNat 32 (p / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [hi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

theorem mul_lt (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_of_lt b.isLt) (by decide))
    (by decide)

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

/-- `mul edx`: `edx:eax := eax · edx`. -/
theorem wp_mulEdx
    (k : ∀ s', Only [.eax, .edx] s s' →
      Pair s' .eax .edx (BitVec.ofNat 64 ((s.gpr .eax).toNat * (s.gpr .edx).toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.mul .edx :: rest)) s Q := by
  refine VG.Proof.Sha256.X86.Stream.WP.cons (s' := execMul .edx s) rfl (k _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ ⟨?_, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  · simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false, ite_true,
      VG.Proof.Argon2.X86.lo_ofNat]
  · simp only [execMul, RegUpd.gpr_setReg, ite_true, VG.Proof.Argon2.X86.hi_ofNat (VG.Proof.Argon2.X86.mul_lt _ _)]

end

/-! ## `addMul` -/

theorem and_low (x : BitVec 64) : x &&& 0xffffffff = BitVec.ofNat 64 (lo x).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, lo_toNat,
    show (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]

theorem addMul_eq (a b : BitVec 64) :
    BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) + BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) +
      b + a = Spec.Argon2.addMul a b := by
  have hp : BitVec.ofNat 64 ((lo a).toNat * (lo b).toNat) = (a &&& 0xffffffff) * (b &&& 0xffffffff) := by
    rw [VG.Proof.Argon2.X86.and_low, VG.Proof.Argon2.X86.and_low, BitVec.ofNat_mul]
  rw [hp, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = x
  have two : (2 : BitVec 64) * x = x + x := by bv_omega
  rw [two]
  ac_rfl

section
variable {B : BitVec 32} {N : Nat}

theorem addMul_ok {a b : Nat} (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (addMul a b)) s fun t => VG.Proof.Argon2.X86.Keep s t ∧
      t.mem = write64 s.mem B a (Spec.Argon2.addMul (rd64 s.mem B a) (rd64 s.mem B b)) := by
  rw [← List.append_nil (addMul a b)]
  unfold addMul
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem h0 (mem_rd (hA b (by omega)))) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [u₁.other _ (by decide), h0]
  refine wp_movS (readSrc_mem b₁ (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA a (by omega))))
    fun s₂ u₂ => ?_
  refine VG.Proof.Argon2.X86.wp_mulEdx fun s₃ o₃ p₃ => ?_
  have O₃ := ((Only.of_upd u₁).trans (Only.of_upd u₂)).trans o₃
  have b₃ : s₃.gpr .esi = B := by rw [O₃.gpr _ (by decide), h0]
  refine wp_add64 (by decide) (by decide) p₃ p₃ fun s₄ o₄ p₄ => ?_
  have O₄ := O₃.trans o₄
  have b₄ : s₄.gpr .esi = B := by rw [O₄.gpr _ (by decide), h0]
  refine wp_add64m (by decide) (by decide) b₄ (O₄.wr ▸ hA) hb p₄ fun s₅ o₅ p₅ => ?_
  have O₅ := O₄.trans o₅
  have b₅ : s₅.gpr .esi = B := by rw [O₅.gpr _ (by decide), h0]
  refine wp_add64m (by decide) (by decide) b₅ (O₅.wr ▸ hA) ha p₅ fun s₆ o₆ p₆ => ?_
  have O₆ := O₅.trans o₆
  have b₆ : s₆.gpr .esi = B := by rw [O₆.gpr _ (by decide), h0]
  refine wp_st b₆ (O₆.wr ▸ hA) ha p₆ fun s₇ u₇ => WP.block_nil
    ⟨Keep.of_wrote O₆ u₇ (by decide), ?_⟩
  have ea : s₂.gpr .eax = lo (rd64 s.mem B a) := by rw [u₂.gpr, u₁.mem, lo_rd64]
  have ed : s₂.gpr .edx = lo (rd64 s.mem B b) := by rw [u₂.other _ (by decide), u₁.gpr, lo_rd64]
  have e₄ : s₄.mem = s.mem := O₄.mem
  have e₅ : s₅.mem = s.mem := O₅.mem
  rw [u₇.mem, O₆.mem]
  simp only [e₄, e₅]
  rw [← VG.Proof.Argon2.X86.addMul_eq, ← ea, ← ed]
/-! ## The rotations -/

theorem xorLd_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {rest : List Instr} {s : State}
    {Q : State → Prop} (h0 : s.gpr .esi = B) (hA : Acc s.wr B N)
    (k : ∀ s', Only [.eax, .edx] s s' → Pair s' .eax .edx (rd64 s.mem B d ^^^ rd64 s.mem B a) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (xorLd d a ++ rest)) s Q := by
  unfold xorLd
  simp only [List.append_assoc]
  refine wp_ld (by decide) (by decide) h0 hA hd fun s₁ o₁ p₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [o₁.gpr _ (by decide), h0]
  simp only [xor64m, VG.Impl.Sha512.X86.sc, List.cons_append, List.nil_append]
  refine wp_xorS (readSrc_mem b₁ (by rw [o₁.rd, o₁.wr]; exact mem_rd (hA a (by omega))))
    fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), b₁]
  have r₂ : InRegions (s₂.rd ++ s₂.wr) (addr B (a + 4)) 4 := by
    rw [u₂.rd, u₂.wr, o₁.rd, o₁.wr]; exact mem_rd (hA (a + 4) (by omega))
  refine wp_xorS (readSrc_mem b₂ r₂) fun s₃ u₃ =>
    k s₃ ((o₁.trans (Only.of_upd u₂)).trans (Only.of_upd u₃) |>.mono (by decide)) ⟨?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, p₁.1, o₁.mem]; simp only [lo_xor, lo_rd64]
  · rw [u₃.gpr, u₂.other _ (by decide), p₁.2, u₂.mem, o₁.mem]; simp only [hi_xor, hi_rd64]

theorem xorRot32_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot32 d a)) s fun t => VG.Proof.Argon2.X86.Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 32) := by
  rw [← List.append_nil (xorRot32 d a)]
  unfold xorRot32
  simp only [List.append_assoc]
  refine VG.Proof.Argon2.X86.xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_st (by rw [o₁.gpr _ (by decide), h0]) (o₁.wr ▸ hA) hd p₁.swap fun s₂ u₂ =>
    WP.block_nil ⟨Keep.of_wrote o₁ u₂ (by decide), by rw [u₂.mem, o₁.mem]⟩

theorem xorRot_ok {d a n : Nat} (hn : 0 < n) (hn' : n < 32) (hd : d + 8 ≤ N) (ha : a + 8 ≤ N)
    {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot d a n)) s fun t => VG.Proof.Argon2.X86.Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight n) := by
  rw [← List.append_nil (xorRot d a n)]
  unfold xorRot
  simp only [List.append_assoc]
  refine VG.Proof.Argon2.X86.xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_rot hn hn' (by decide) (by decide) (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O := o₁.trans o₂
  refine wp_st (by rw [O.gpr _ (by decide), h0]) (O.wr ▸ hA) hd p₂ fun s₃ u₃ =>
    WP.block_nil ⟨Keep.of_wrote O u₃ (by decide), by rw [u₃.mem, O.mem]⟩

theorem xorRot63_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot63 d a)) s fun t => VG.Proof.Argon2.X86.Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 63) := by
  rw [← List.append_nil (xorRot63 d a)]
  unfold xorRot63
  simp only [List.append_assoc]
  refine VG.Proof.Argon2.X86.xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_rot' (by decide) (by decide) (by decide) (by decide) (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O := o₁.trans o₂
  refine wp_st (by rw [O.gpr _ (by decide), h0]) (O.wr ▸ hA) hd p₂ fun s₃ u₃ =>
    WP.block_nil ⟨Keep.of_wrote O u₃ (by decide), by rw [u₃.mem, O.mem]⟩

end

end VG.Proof.Argon2.X86

end

/-!
# Argon2 on x86 (32-bit): GB on the permuted block

The permuted block in `scratch[1024, 2048)` as a vector of words
(`working`), and `gbAt_ok`: one GB updates it as `Proof.Argon2.mixWords`, and
writes nothing else.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (wOff gb gbAt)
open VG.Proof.Sha512.X86 (Acc rd64 write64 rd64_write64_self rd64_write64_ne)

/-- The permuted block, at `B + 1024`. -/
def working (m : Mem) (B : BitVec 32) : Block := Vector.ofFn fun i => rd64 m B (wOff i.val)

theorem working_get (m : Mem) (B : BitVec 32) (i : Fin 128) :
    (VG.Proof.Argon2.X86.working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [VG.Proof.Argon2.X86.working, Fin.getElem_fin, Vector.getElem_ofFn]

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : Word) :
    VG.Proof.Argon2.X86.working (write64 m B (wOff i.val) v) B = (VG.Proof.Argon2.X86.working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true]
    exact rd64_write64_self m v (by simp only [wOff]; omega)
  · simp only [h, ite_false]
    exact rd64_write64_ne m v (by simp only [wOff]; omega) (by simp only [wOff]; omega)
      (by simp only [wOff]; omega)

/-- The permuted block's region. -/
abbrev permR (B : BitVec 32) : Region := ⟨addr B 1024, 1024⟩

theorem addr_off {d : Nat} (hd : d < 4096) : addr B d = B.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by omega)

/-- A write to a word of the permuted block stays in its region. -/
theorem frame_write (m m' : Mem) (hf : Frame [VG.Proof.Argon2.X86.permR B] m m') (i : Fin 128) (v : Word) :
    Frame [VG.Proof.Argon2.X86.permR B] m (write64 m' B (wOff i.val) v) := by
  have c : ∀ e, e + 4 ≤ 1024 → (VG.Proof.Argon2.X86.permR B).Contains (addr B (1024 + e)) (32 / 8) := fun e he => by
    show (⟨addr B 1024, 1024⟩ : Region).Contains _ _
    rw [VG.Proof.Argon2.X86.addr_off hfit (by omega), VG.Proof.Argon2.X86.addr_off hfit (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  have m₁ := List.mem_singleton_self (VG.Proof.Argon2.X86.permR B)
  have := i.isLt
  exact (hf.writeW m₁ _ (c (8 * i.val) (by omega))).writeW m₁ _
    (by rw [show wOff i.val + 4 = 1024 + (8 * i.val + 4) by simp only [wOff]; omega]
        exact c _ (by omega))

end

/-- `v[a] := addMul(v[a], v[b])` -/
def am {n : Nat} (a b : Fin n) (v : Vector Word n) : Vector Word n := v.set a (addMul v[a] v[b])

/-- `v[d] := (v[d] ^ v[a]) >>> r` -/
def xr {n : Nat} (d a : Fin n) (r : Nat) (v : Vector Word n) : Vector Word n :=
  v.set d ((v[d] ^^^ v[a]).rotateRight r)

/-- GB on any vector of words: `Spec.Argon2.GB`'s updates. -/
def gbV {n : Nat} (v : Vector Word n) (a b c d : Fin n) : Vector Word n :=
  VG.Proof.Argon2.X86.xr b c 63 (VG.Proof.Argon2.X86.am c d (VG.Proof.Argon2.X86.xr d a 16 (VG.Proof.Argon2.X86.am a b (VG.Proof.Argon2.X86.xr b c 24 (VG.Proof.Argon2.X86.am c d (VG.Proof.Argon2.X86.xr d a 32 (VG.Proof.Argon2.X86.am a b v)))))))

set_option linter.unusedSimpArgs false in
theorem gbV_eq {n : Nat} (v : Vector Word n) {a b c d : Fin n} (hab : a.val ≠ b.val)
    (hac : a.val ≠ c.val) (had : a.val ≠ d.val) (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val)
    (hcd : c.val ≠ d.val) : VG.Proof.Argon2.X86.gbV v a b c d = Proof.Argon2.mixWords v a b c d := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.gbV, VG.Proof.Argon2.X86.am, VG.Proof.Argon2.X86.xr, Proof.Argon2.mixWords, Proof.Argon2.mix, Fin.getElem_fin, Vector.getElem_set,
    hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc,
    Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  have nb := Ne.symm hab; have nc := Ne.symm hac; have nd := Ne.symm had
  have nc' := Ne.symm hbc; have nd' := Ne.symm hbd; have nd'' := Ne.symm hcd
  by_cases eb : b.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', ite_true, ite_false]
  by_cases ec : c.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ite_true, ite_false]
  by_cases ed : d.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ec, ite_true, ite_false]
  by_cases ea : a.val = j
  · subst j
    simp only [hab, hac, had, hbc, hbd, hcd, nb, nc, nd, nc', nd', nd'', eb, ec, ed, ite_true, ite_false]
  simp only [eb, ec, ed, ea, ite_false]

/-! ## GB -/

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

/-- What a step of GB leaves: the registers but GB's, and the memory at `B`
with the permuted block `v` in place of the old one, `Frame [permR B]`. -/
structure Step (B : BitVec 32) (s : State) (v : Block) (t : State) : Prop where
  keep : VG.Proof.Argon2.X86.Keep s t
  working : VG.Proof.Argon2.X86.working t.mem B = v
  frame : Frame [VG.Proof.Argon2.X86.permR B] s.mem t.mem

theorem Step.trans {s t u : State} {v w : Block} (h : VG.Proof.Argon2.X86.Step B s v t) (h' : VG.Proof.Argon2.X86.Step B t w u) :
    VG.Proof.Argon2.X86.Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

include hfit

theorem step_write {s t : State} (k : VG.Proof.Argon2.X86.Keep s t) {i : Fin 128} {x : Word}
    (hm : t.mem = write64 s.mem B (wOff i.val) x) :
    VG.Proof.Argon2.X86.Step B s ((VG.Proof.Argon2.X86.working s.mem B).set i x) t :=
  ⟨k, by rw [hm, VG.Proof.Argon2.X86.working_write hfit], by rw [hm]; exact VG.Proof.Argon2.X86.frame_write hfit _ _ (Frame.refl _ _) i x⟩

theorem Step.am {s t t' : State} {v : Block} (S : VG.Proof.Argon2.X86.Step B s v t) (k : VG.Proof.Argon2.X86.Keep t t') {a b : Fin 128}
    (m : t'.mem = write64 t.mem B (wOff a.val)
      (Spec.Argon2.addMul (rd64 t.mem B (wOff a.val)) (rd64 t.mem B (wOff b.val)))) :
    VG.Proof.Argon2.X86.Step B s (VG.Proof.Argon2.X86.am a b v) t' := by
  have st := VG.Proof.Argon2.X86.step_write hfit k m
  rw [← VG.Proof.Argon2.X86.working_get, ← VG.Proof.Argon2.X86.working_get, S.working] at st
  exact S.trans st

theorem Step.xr {s t t' : State} {v : Block} (S : VG.Proof.Argon2.X86.Step B s v t) (k : VG.Proof.Argon2.X86.Keep t t') {d a : Fin 128} {r : Nat}
    (m : t'.mem = write64 t.mem B (wOff d.val)
      ((rd64 t.mem B (wOff d.val) ^^^ rd64 t.mem B (wOff a.val)).rotateRight r)) :
    VG.Proof.Argon2.X86.Step B s (VG.Proof.Argon2.X86.xr d a r v) t' := by
  have st := VG.Proof.Argon2.X86.step_write hfit k m
  rw [← VG.Proof.Argon2.X86.working_get, ← VG.Proof.Argon2.X86.working_get, S.working] at st
  exact S.trans st

theorem gbAt_ok {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B 4096) (a b c d : Fin 128) :
    WP isa (gbAt a.val b.val c.val d.val) s (VG.Proof.Argon2.X86.Step B s (VG.Proof.Argon2.X86.gbV (VG.Proof.Argon2.X86.working s.mem B) a b c d)) := by
  have o : ∀ i : Fin 128, wOff i.val + 8 ≤ 4096 := fun i => by
    have := i.isLt; simp only [wOff]; omega
  have S₀ : VG.Proof.Argon2.X86.Step B s (VG.Proof.Argon2.X86.working s.mem B) s := ⟨.refl s, rfl, Frame.refl _ _⟩
  have e : ∀ {t : State} {v : Block}, VG.Proof.Argon2.X86.Step B s v t → t.gpr .esi = B := fun S => S.keep.esi.trans h0
  have A : ∀ {t : State} {v : Block}, VG.Proof.Argon2.X86.Step B s v t → Acc t.wr B 4096 := fun S => S.keep.wr ▸ hA
  unfold gbAt gb
  refine WP.block_append ((VG.Proof.Argon2.X86.addMul_ok (o a) (o b) (e S₀) (A S₀)).mono fun s₁ ⟨k₁, m₁⟩ => ?_)
  have S₁ := S₀.am hfit k₁ m₁
  refine WP.block_append ((VG.Proof.Argon2.X86.xorRot32_ok (o d) (o a) (e S₁) (A S₁)).mono fun s₂ ⟨k₂, m₂⟩ => ?_)
  have S₂ := S₁.xr hfit k₂ m₂
  refine WP.block_append ((VG.Proof.Argon2.X86.addMul_ok (o c) (o d) (e S₂) (A S₂)).mono fun s₃ ⟨k₃, m₃⟩ => ?_)
  have S₃ := S₂.am hfit k₃ m₃
  refine WP.block_append ((VG.Proof.Argon2.X86.xorRot_ok (by decide) (by decide) (o b) (o c) (e S₃) (A S₃)).mono
    fun s₄ ⟨k₄, m₄⟩ => ?_)
  have S₄ := S₃.xr hfit k₄ m₄
  refine WP.block_append ((VG.Proof.Argon2.X86.addMul_ok (o a) (o b) (e S₄) (A S₄)).mono fun s₅ ⟨k₅, m₅⟩ => ?_)
  have S₅ := S₄.am hfit k₅ m₅
  refine WP.block_append ((VG.Proof.Argon2.X86.xorRot_ok (by decide) (by decide) (o d) (o a) (e S₅) (A S₅)).mono
    fun s₆ ⟨k₆, m₆⟩ => ?_)
  have S₆ := S₅.xr hfit k₆ m₆
  refine WP.block_append ((VG.Proof.Argon2.X86.addMul_ok (o c) (o d) (e S₆) (A S₆)).mono fun s₇ ⟨k₇, m₇⟩ => ?_)
  have S₇ := S₆.am hfit k₇ m₇
  exact (VG.Proof.Argon2.X86.xorRot63_ok (o b) (o c) (e S₇) (A S₇)).mono fun s₈ ⟨k₈, m₈⟩ => S₇.xr hfit k₈ m₈

end

end VG.Proof.Argon2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.Compress`. -/
section

section

section

section

/-!
# Argon2 on x86 (32-bit): the row and column permutations

As on x86-64 (`Proof/Argon2/X86_64/Compress.lean`): P on any injectively
selected row or column (`permuteAt_ok`), and the rows and columns
(`rounds_ok`).
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.X86 (Acc)


/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (VG.Proof.Argon2.X86.working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (VG.Proof.Argon2.X86.working m B)[k] = b[k]

/-- The base and the permissions of `scratch`, and the rest of a `Step`. -/
def At (B : BitVec 32) (s : State) : Prop := s.gpr .esi = B ∧ Acc s.wr B 4096

theorem At.of_step {B : BitVec 32} {s t : State} {v : Block} (h : VG.Proof.Argon2.X86.At B s) (st : VG.Proof.Argon2.X86.Step B s v t) : VG.Proof.Argon2.X86.At B t :=
  ⟨st.keep.esi.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

include hfit

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : VG.Proof.Argon2.X86.At B s) (base : Block) (v : Vector Word 16) (hv : VG.Proof.Argon2.X86.Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val) s
      fun t => VG.Proof.Argon2.X86.Holds index base (GB v a b c d) t.mem B ∧
        ∃ w, VG.Proof.Argon2.X86.Step B s w t := by
  have ne : ∀ {x y : Fin 16}, x.val ≠ y.val → (index x).val ≠ (index y).val :=
    fun h e => h (congrArg Fin.val (hi (Fin.ext e)))
  refine (VG.Proof.Argon2.X86.gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)).mono fun t st => ?_
  rw [VG.Proof.Argon2.X86.gbV_eq _ (ne hab) (ne hac) (ne had) (ne hbc) (ne hbd) (ne hcd)] at st
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : VG.Proof.Argon2.X86.At B s) (base : Block) (v : Vector Word 16) (hv : VG.Proof.Argon2.X86.Holds index base v s.mem B) :
    WP isa (Impl.Argon2.X86.permuteAt index) s fun t =>
      VG.Proof.Argon2.X86.Holds index base (permute v) t.mem B ∧ ∃ w, VG.Proof.Argon2.X86.Step B s w t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : VG.Proof.Argon2.X86.Holds index base v' t.mem B ∧ ∃ w, VG.Proof.Argon2.X86.Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => VG.Proof.Argon2.X86.Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, VG.Proof.Argon2.X86.Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (VG.Proof.Argon2.X86.step_ok hfit index hi (hs.of_step st) base v' hh a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, w', st'⟩
    exact ⟨hu, w', st.trans st'⟩
  unfold Impl.Argon2.X86.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, _, ⟨.refl s, rfl, Frame.refl _ _⟩⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : VG.Proof.Argon2.X86.At B s) :
    WP isa (Impl.Argon2.X86.permuteAt index) s
      (VG.Proof.Argon2.X86.Step B s (Spec.Argon2.permuteAt index (VG.Proof.Argon2.X86.working s.mem B))) := by
  refine (VG.Proof.Argon2.X86.permuteAt_holds hfit index hi hs (VG.Proof.Argon2.X86.working s.mem B)
    (gather index (VG.Proof.Argon2.X86.working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

/-- A list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8)) {s : State} (hs : VG.Proof.Argon2.X86.At B s) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.X86.permuteAt (index i)) rest)
      (.block [])) s
      (VG.Proof.Argon2.X86.Step B s (is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (VG.Proof.Argon2.X86.working s.mem B))) := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨.refl s, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.X86.permuteAt_ok hfit (index i) (hi i) hs).mono ?_
    intro t st
    refine (ih (hs.of_step st)).mono ?_
    intro u st'
    refine st.trans ?_
    rw [List.foldl_cons, ← st.working]
    exact st'

end

end VG.Proof.Argon2.X86

end

/-!
# Argon2 on x86 (32-bit): blocks as 32-bit words

A block at `B + o` (`blk m B o`) as 64-bit words, each the pair of 32-bit words
the code copies: `blk_of_words` builds it from them, `blockAt_eq` relates it to
the contract's `Spec.Argon2.blockAt`, and `xor_words` XORs two blocks word by
word.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (rd64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_append hi_append eq_of_lo_hi)

/-- The block at `B + o`, as pairs of 32-bit words. -/
def blk (m : Mem) (B : BitVec 32) (o : Nat) : Block := Vector.ofFn fun j => rd64 m B (o + 8 * j.val)

/-- The block made of the 32-bit words `f 0, f 1, …` (two per 64-bit word, the low one first). -/
def ofWords (f : Nat → BitVec 32) : Block := Vector.ofFn fun j => f (2 * j.val + 1) ++ f (2 * j.val)

theorem blk_of_words {m : Mem} {B : BitVec 32} {o : Nat} {f : Nat → BitVec 32}
    (h : ∀ i < 256, m.readW (addr B (o + 4 * i)) 32 = f i) : VG.Proof.Argon2.X86.blk m B o = VG.Proof.Argon2.X86.ofWords f := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.blk, VG.Proof.Argon2.X86.ofWords, Vector.getElem_ofFn, rd64]
  rw [show o + 8 * j + 4 = o + 4 * (2 * j + 1) by omega, show o + 8 * j = o + 4 * (2 * j) by omega,
    h _ (by omega), h _ (by omega)]

theorem working_eq (m : Mem) (B : BitVec 32) : VG.Proof.Argon2.X86.working m B = VG.Proof.Argon2.X86.blk m B 1024 := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.working, VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, Impl.Argon2.X86.wOff]

theorem blockAt_eq {m : Mem} {B : BitVec 32} (hfit : B.toNat + 1024 ≤ 2 ^ 32) :
    blockAt m (B.setWidth 64) = VG.Proof.Argon2.X86.blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, Nat.zero_add]
  rw [Proof.Blake2.X86.CompressB.rd64_eq (by omega)]
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem append_xor (a b c d : BitVec 32) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  eq_of_lo_hi (by rw [lo_xor, lo_append, lo_append, lo_append])
    (by rw [hi_xor, hi_append, hi_append, hi_append])

theorem xor_words (f g : Nat → BitVec 32) :
    xorBlock (VG.Proof.Argon2.X86.ofWords f) (VG.Proof.Argon2.X86.ofWords g) = VG.Proof.Argon2.X86.ofWords fun i => f i ^^^ g i := by
  apply Vector.ext
  intro j hj
  simp only [xorBlock, VG.Proof.Argon2.X86.ofWords, Vector.getElem_zipWith, Vector.getElem_ofFn, VG.Proof.Argon2.X86.append_xor]

/-- A prefix of `n` 32-bit words at `B + o` holds `f`. -/
def Words (m : Mem) (B : BitVec 32) (o : Nat) (f : Nat → BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, m.readW (addr B (o + 4 * i)) 32 = f i

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): the contract of the proof

`compressX86`: the contract the proof is written against, with the arguments
on the stack only read; `Spec.Argon2.compressContract`, which lets the code
write them, is reached by narrowing (`Proof/Argon2/X86/CompressVerified.lean`).
`Pre` names the facts of its precondition.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (Acc mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr)

/-- `vg_argon2_compress(x, y, out, scratch)`: reads the arguments (16 bytes
above the return address) and the two input blocks, writes the output block
and 4096 bytes of scratch. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let x : Region := ⟨(arg s 0).setWidth 64, 1024⟩
    let y : Region := ⟨(arg s 1).setWidth 64, 1024⟩
    let out : Region := ⟨(arg s 2).setWidth 64, 1024⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [x, y, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧
    y.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
    ret.Disjoint scratch ∧
    (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 1024 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := blockAt s'.mem ((arg s 2).setWidth 64) =
    compress (blockAt s.mem ((arg s 0).setWidth 64)) (blockAt s.mem ((arg s 1).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev xp : BitVec 32 := arg s₀ 0
abbrev yp : BitVec 32 := arg s₀ 1
abbrev op : BitVec 32 := arg s₀ 2
abbrev scr : BitVec 32 := arg s₀ 3
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev xR : Region := ⟨(VG.Proof.Argon2.X86.xp s₀).setWidth 64, 1024⟩
abbrev yR : Region := ⟨(VG.Proof.Argon2.X86.yp s₀).setWidth 64, 1024⟩
abbrev outR : Region := ⟨(VG.Proof.Argon2.X86.op s₀).setWidth 64, 1024⟩
abbrev scrR : Region := ⟨(VG.Proof.Argon2.X86.scr s₀).setWidth 64, 4096⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.Argon2.X86.esp₀ s₀).setWidth 64, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.X86.xR s₀, VG.Proof.Argon2.X86.yR s₀, VG.Proof.Argon2.X86.argR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀]
  out_scr : (VG.Proof.Argon2.X86.outR s₀).Disjoint (VG.Proof.Argon2.X86.scrR s₀)
  x_out : (VG.Proof.Argon2.X86.xR s₀).Disjoint (VG.Proof.Argon2.X86.outR s₀)
  x_scr : (VG.Proof.Argon2.X86.xR s₀).Disjoint (VG.Proof.Argon2.X86.scrR s₀)
  y_out : (VG.Proof.Argon2.X86.yR s₀).Disjoint (VG.Proof.Argon2.X86.outR s₀)
  y_scr : (VG.Proof.Argon2.X86.yR s₀).Disjoint (VG.Proof.Argon2.X86.scrR s₀)
  arg_out : (VG.Proof.Argon2.X86.argR s₀).Disjoint (VG.Proof.Argon2.X86.outR s₀)
  arg_scr : (VG.Proof.Argon2.X86.argR s₀).Disjoint (VG.Proof.Argon2.X86.scrR s₀)
  ret_out : (VG.Proof.Argon2.X86.retR s₀).Disjoint (VG.Proof.Argon2.X86.outR s₀)
  ret_scr : (VG.Proof.Argon2.X86.retR s₀).Disjoint (VG.Proof.Argon2.X86.scrR s₀)
  x_fits : (VG.Proof.Argon2.X86.xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (VG.Proof.Argon2.X86.yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.X86.op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.X86.scr s₀).toNat + 4096 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Argon2.X86.esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressX86.pre s₀) : VG.Proof.Argon2.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (VG.Proof.Argon2.X86.scr s₀) 4096 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem out_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (addr (VG.Proof.Argon2.X86.op s₀) d) 4 :=
  ⟨VG.Proof.Argon2.X86.outR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.out_fits⟩

theorem in_x {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.xp s₀) d) 4 :=
  ⟨VG.Proof.Argon2.X86.xR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.x_fits⟩

theorem in_y {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.yp s₀) d) 4 :=
  ⟨VG.Proof.Argon2.X86.yR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.y_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (VG.Proof.Argon2.X86.esp₀ s₀) d = (VG.Proof.Argon2.X86.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Argon2.X86.argR s₀).Contains (addr (VG.Proof.Argon2.X86.esp₀ s₀) d) 4 := by
  show (⟨addr (VG.Proof.Argon2.X86.esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Argon2.X86.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Argon2.X86.argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument is unchanged while only `out` and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem m) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 20) : m.readW (addr (VG.Proof.Argon2.X86.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Argon2.X86.esp₀ s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.X86.argR s₀) (hp.arg_contains hd hd') ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_out, hp.arg_scr⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (VG.Proof.Argon2.X86.xp s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Argon2.X86.xp s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.X86.xR s₀) (contains_addr hd (by omega) hp.x_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (VG.Proof.Argon2.X86.yp s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Argon2.X86.yp s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.X86.yR s₀) (contains_addr hd (by omega) hp.y_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [VG.Proof.Argon2.X86.outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (addr (VG.Proof.Argon2.X86.scr s₀) d) 32 = m.readW (addr (VG.Proof.Argon2.X86.scr s₀) d) 32 := by
  refine hf.readW (r := VG.Proof.Argon2.X86.scrR s₀) (contains_addr hd (by omega) hp.scr_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): correctness

The prologue (`prologue_ok`), the initialization of both halves of scratch
with X XOR Y (`init_ok`, one word at a time), the rows and columns
(`Proof/Argon2/X86/Rounds.lean`), and the epilogue writing the output and
restoring `esi` (`epilogue_ok`): `correct`.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_mov readW_writeW_addr)

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (addr (VG.Proof.Argon2.X86.xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (addr (VG.Proof.Argon2.X86.yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = VG.Proof.Argon2.X86.scr s₀
  ecx : s.gpr .ecx = VG.Proof.Argon2.X86.xp s₀
  edx : s.gpr .edx = VG.Proof.Argon2.X86.yp s₀
  regs : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem s.mem
  saved : s.mem.readW (addr (VG.Proof.Argon2.X86.scr s₀) savedOff) 32 = s₀.gpr .esi
  low : VG.Proof.Argon2.X86.Words s.mem (VG.Proof.Argon2.X86.scr s₀) 0 (VG.Proof.Argon2.X86.xy s₀) n
  high : VG.Proof.Argon2.X86.Words s.mem (VG.Proof.Argon2.X86.scr s₀) 1024 (VG.Proof.Argon2.X86.xy s₀) n

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (VG.Proof.Argon2.X86.scrR s₀).Contains (addr (VG.Proof.Argon2.X86.scr s₀) d) (32 / 8) :=
  contains_addr hd (by omega) hp.scr_fits

theorem prologue_ok :
    WP isa (.block prologue) s₀ (VG.Proof.Argon2.X86.InitInv s₀ · 0) := by
  have hm : VG.Proof.Argon2.X86.scrR s₀ ∈ [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] := by simp
  unfold prologue
  refine wp_movm (ea_of rfl 16) (hp.in_arg (d := 16) rfl (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.Argon2.X86.scr s₀ := u₁.gpr
  refine wp_store (ea_of e₁ savedOff) (by rw [u₁.wr]; exact hp.acc rfl _ (by decide)) fun s₂ u₂ => ?_
  have f₂ : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW hm _ (VG.Proof.Argon2.X86.scr_contains hp (by decide))
  refine wp_mov fun s₃ u₃ => ?_
  have sp₃ : s₃.gpr .esp = VG.Proof.Argon2.X86.esp₀ s₀ := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_movm (ea_of sp₃ 4) (by rw [u₃.rd, u₂.rd, u₁.rd, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 4) rfl (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), sp₃]) 8)
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 8) rfl (by omega) (by omega)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, e₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · intro r h0 h6 h1 h2
    rw [u₅.other _ h2, u₄.other _ h1, u₃.other _ h6, u₂.gpr, u₁.other _ h0]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [m₅]; exact f₂
  · rw [m₅, u₂.mem, Mem.readW_writeW_self32, u₁.other _ (by decide)]

/-- One word of the initialization. -/
theorem initWord_ok {s : State} {n : Nat} (hn : n < 256) (h : VG.Proof.Argon2.X86.InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (VG.Proof.Argon2.X86.InitInv s₀ · (n + 1)) := by
  have hm : VG.Proof.Argon2.X86.scrR s₀ ∈ [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] := by simp
  have fits := hp.scr_fits
  unfold initWord
  refine wp_movm (ea_of h.ecx _) (hp.in_x h.rd (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.edx]) (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = VG.Proof.Argon2.X86.xy s₀ n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.x_frame h.frame (by omega), hp.y_frame h.frame (by omega)]; rfl
  have esi₂ : s₂.gpr .esi = VG.Proof.Argon2.X86.scr s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  refine wp_store (ea_of esi₂ _) (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega))
    fun s₃ u₃ => ?_
  have w₃ : InRegions s₃.wr (addr (VG.Proof.Argon2.X86.scr s₀) (1024 + 4 * n)) 4 := by
    rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega)
  refine wp_store (ea_of (by rw [u₃.gpr, esi₂]) _) w₃ fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (addr (VG.Proof.Argon2.X86.scr s₀) (4 * n)) (VG.Proof.Argon2.X86.xy s₀ n)).writeW
      (addr (VG.Proof.Argon2.X86.scr s₀) (1024 + 4 * n)) (VG.Proof.Argon2.X86.xy s₀ n) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, v₂]
  have r₄ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₄.mem.readW (addr (VG.Proof.Argon2.X86.scr s₀) e) 32 = s.mem.readW (addr (VG.Proof.Argon2.X86.scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) h2,
      readW_writeW_addr _ _ (by omega) (by omega) h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.gpr, esi₂]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · intro r h0 h6 h1 h2
    rw [u₄.gpr, u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h6 h1 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₄]
    exact (h.frame.writeW hm _ (VG.Proof.Argon2.X86.scr_contains hp (by omega))).writeW hm _ (VG.Proof.Argon2.X86.scr_contains hp (by omega))
  · rw [r₄ _ (by decide) (by simp only [savedOff]; omega) (by simp only [savedOff]; omega)]
    exact h.saved
  · intro i hi
    by_cases e : i = n
    · subst e
      rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) (by omega), Nat.zero_add,
        Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.low i (by omega)
  · intro i hi
    by_cases e : i = n
    · subst e; rw [m₄, Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.high i (by omega)

theorem init_ok {s : State} (h : VG.Proof.Argon2.X86.InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (VG.Proof.Argon2.X86.InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => VG.Proof.Argon2.X86.initWord_ok hp (by omega) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (addr B (1024 + 4 * i)) 32 ^^^ m.readW (addr B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = VG.Proof.Argon2.X86.scr s₀
  ecx : s.gpr .ecx = VG.Proof.Argon2.X86.op s₀
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Argon2.X86.outR s₀] s₄.mem s.mem
  out : VG.Proof.Argon2.X86.Words s.mem (VG.Proof.Argon2.X86.op s₀) 0 (VG.Proof.Argon2.X86.outWord (VG.Proof.Argon2.X86.scr s₀) s₄.mem) n

section
variable {s₀ : State} (hp : VG.Proof.Argon2.X86.Pre s₀)
include hp

theorem finishWord_ok {s₄ s : State} {n : Nat} (hn : n < 256) (h : VG.Proof.Argon2.X86.FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (VG.Proof.Argon2.X86.FinInv s₀ s₄ · (n + 1)) := by
  have hm : VG.Proof.Argon2.X86.outR s₀ ∈ [VG.Proof.Argon2.X86.outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  unfold finishWord
  refine wp_movm (ea_of h.esi _) (hp.in_scr h.wr (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.esi]) (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = VG.Proof.Argon2.X86.outWord (VG.Proof.Argon2.X86.scr s₀) s₄.mem n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.scr_frame h.frame (by omega), hp.scr_frame h.frame (by omega)]; rfl
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]) _)
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.out_wr rfl (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem.writeW (addr (VG.Proof.Argon2.X86.op s₀) (4 * n)) (VG.Proof.Argon2.X86.outWord (VG.Proof.Argon2.X86.scr s₀) s₄.mem n) := by
    rw [u₃.mem, u₂.mem, u₁.mem, v₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · intro r h0 h1
    rw [u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h1]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₃]; exact h.frame.writeW hm _ (contains_addr (by omega) (by omega) fits)
  · intro i hi
    rw [m₃, Nat.zero_add]
    by_cases e : i = n
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
      have := h.out i (by omega); rwa [Nat.zero_add] at this

theorem finish_ok {s₄ s : State} (h : VG.Proof.Argon2.X86.FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (VG.Proof.Argon2.X86.FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => VG.Proof.Argon2.X86.finishWord_ok hp (by omega) ht)

end

end VG.Proof.Argon2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.CompressLit`. -/
section

/-!
# Argon2 compression on x86 (32-bit): the code as a literal

The compression function is fully unrolled: its literal (`materialize_code`)
spares the kernel building the instructions in every check that evaluates
the code (constant time, `spSafe`), and its callers call it.
-/

namespace VG.Impl.Argon2.X86

materialize_code VG.Impl.Argon2.X86.compress

end VG.Impl.Argon2.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86.CompressVerified`. -/
section

section

/-!
# Argon2 compression on x86 (32-bit): the whole function

`correct`: the prologue, the initialization, the rows and columns and the
epilogue, with the calling convention's obligations.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr wp_movm)

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem permR_sub : Region.Sub (VG.Proof.Argon2.X86.permR B) ⟨B.setWidth 64, 4096⟩ := by
  show Region.Sub ⟨addr B 1024, 1024⟩ _
  rw [VG.Proof.Argon2.X86.addr_off hfit (by decide)]
  exact Offset.sub_base _ (by decide)

/-- A word of `scratch` outside the permuted block is unchanged by its writes. -/
theorem outside_perm {m m' : Mem} (hf : Frame [VG.Proof.Argon2.X86.permR B] m m') {d : Nat} (hd : d + 4 ≤ 4096)
    (ho : d + 4 ≤ 1024 ∨ 2048 ≤ d) : m'.readW (addr B d) 32 = m.readW (addr B d) 32 := by
  refine hf.readW (r := ⟨addr B d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  show Region.Disjoint _ ⟨addr B 1024, 1024⟩
  rw [VG.Proof.Argon2.X86.addr_off hfit (by omega), VG.Proof.Argon2.X86.addr_off hfit (by decide)]
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem low_perm {m m' : Mem} (hf : Frame [VG.Proof.Argon2.X86.permR B] m m') : VG.Proof.Argon2.X86.blk m' B 0 = VG.Proof.Argon2.X86.blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86.blk, Vector.getElem_ofFn, rd64]
  rw [VG.Proof.Argon2.X86.outside_perm hfit hf (by omega) (by omega), VG.Proof.Argon2.X86.outside_perm hfit hf (by omega) (by omega)]

end

theorem words_zero {m : Mem} {B : BitVec 32} {f : Nat → BitVec 32} (h : VG.Proof.Argon2.X86.Words m B 0 f 256) :
    VG.Proof.Argon2.X86.blk m B 0 = VG.Proof.Argon2.X86.ofWords f := VG.Proof.Argon2.X86.blk_of_words fun i hi => h i hi

theorem correct {s₀ : State} (hp : VG.Proof.Argon2.X86.Pre s₀) :
    WP isa Impl.Argon2.X86.compress s₀ fun t => abiPreserved s₀ t ∧ compressX86.post s₀ t := by
  have fits := hp.scr_fits
  unfold Impl.Argon2.X86.compress Impl.Argon2.X86.rounds
  refine WP.seq (WP.block_append ((VG.Proof.Argon2.X86.prologue_ok hp).mono fun s₁ h₁ =>
    (VG.Proof.Argon2.X86.init_ok hp h₁ 256 (Nat.le_refl _)).mono fun s₂ h₂ => ?_))
  have A₂ : VG.Proof.Argon2.X86.At (VG.Proof.Argon2.X86.scr s₀) s₂ := ⟨h₂.esi, hp.acc h₂.wr⟩
  refine WP.seq (WP.seq ((VG.Proof.Argon2.X86.rounds_ok fits rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8)
    A₂).mono fun s₃ st₃ => (VG.Proof.Argon2.X86.rounds_ok fits colIndex Proof.Argon2.colIndex_injective
      (List.finRange 8) (A₂.of_step st₃)).mono fun s₄ st₄ => ?_))
  have k₄ := st₃.keep.trans st₄.keep
  have pf : Frame [VG.Proof.Argon2.X86.permR (VG.Proof.Argon2.X86.scr s₀)] s₂.mem s₄.mem := st₃.frame.trans st₄.frame
  have f₄ : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem s₄.mem :=
    h₂.frame.trans (pf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.X86.scrR s₀, by simp, VG.Proof.Argon2.X86.permR_sub fits⟩)
  have g₄ : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s₄.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 =>
    (k₄.gpr r (by simp [VG.Proof.Argon2.X86.temps, h0, h1, h2])).trans (h₂.regs r h0 h6 h1 h2)
  have sp₄ : s₄.gpr .esp = VG.Proof.Argon2.X86.esp₀ s₀ := g₄ _ (by decide) (by decide) (by decide) (by decide)
  unfold epilogue
  simp only [List.cons_append]
  refine wp_movm (ea_of sp₄ 12) (by rw [k₄.rd, k₄.wr, h₂.rd, h₂.wr]; exact hp.in_arg rfl (by omega) (by omega))
    fun s₅ u₅ => ?_
  have h₅ : VG.Proof.Argon2.X86.FinInv s₀ s₄ s₅ 0 :=
    ⟨by rw [u₅.other _ (by decide), k₄.esi, h₂.esi], by rw [u₅.gpr, hp.arg_frame f₄ (by omega) (by omega)]; rfl,
      fun r _ h1 => u₅.other r h1, by rw [u₅.rd, k₄.rd, h₂.rd], by rw [u₅.wr, k₄.wr, h₂.wr],
      by rw [u₅.mem]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine WP.block_append ((VG.Proof.Argon2.X86.finish_ok hp h₅ 256 (Nat.le_refl _)).mono fun s₆ h₆ => ?_)
  refine wp_movm (ea_of h₆.esi savedOff) (hp.in_scr h₆.wr (by decide)) fun t u => WP.block_nil ?_
  have ft : Frame [VG.Proof.Argon2.X86.outR s₀, VG.Proof.Argon2.X86.scrR s₀] s₀.mem t.mem := by
    rw [u.mem]
    exact f₄.trans (h₆.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  have gt : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → t.gpr r = s₀.gpr r := fun r h0 h6 h1 h2 => by
    rw [u.other r h6, h₆.regs r h0 h1, g₄ r h0 h6 h1 h2]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · rw [u.gpr, hp.scr_frame h₆.frame (by decide), VG.Proof.Argon2.X86.outside_perm fits pf (by decide) (by decide)]
      exact h₂.saved
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
    · exact gt _ (by decide) (by decide) (by decide) (by decide)
  · refine ft.readW (r := VG.Proof.Argon2.X86.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hp.ret_out, hp.ret_scr⟩
  · -- The output.
    have R₂ : VG.Proof.Argon2.X86.blk s₂.mem (VG.Proof.Argon2.X86.scr s₀) 0 = VG.Proof.Argon2.X86.ofWords (VG.Proof.Argon2.X86.xy s₀) := VG.Proof.Argon2.X86.words_zero h₂.low
    have W₂ : VG.Proof.Argon2.X86.working s₂.mem (VG.Proof.Argon2.X86.scr s₀) = VG.Proof.Argon2.X86.ofWords (VG.Proof.Argon2.X86.xy s₀) := by
      rw [VG.Proof.Argon2.X86.working_eq]; exact VG.Proof.Argon2.X86.blk_of_words fun i hi => h₂.high i hi
    have X : xorBlock (blockAt s₀.mem ((VG.Proof.Argon2.X86.xp s₀).setWidth 64)) (blockAt s₀.mem ((VG.Proof.Argon2.X86.yp s₀).setWidth 64)) =
        VG.Proof.Argon2.X86.ofWords (VG.Proof.Argon2.X86.xy s₀) := by
      rw [VG.Proof.Argon2.X86.blockAt_eq hp.x_fits, VG.Proof.Argon2.X86.blockAt_eq hp.y_fits,
        VG.Proof.Argon2.X86.blk_of_words (f := fun i => s₀.mem.readW (addr (VG.Proof.Argon2.X86.xp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]),
        VG.Proof.Argon2.X86.blk_of_words (f := fun i => s₀.mem.readW (addr (VG.Proof.Argon2.X86.yp s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), VG.Proof.Argon2.X86.xor_words]
      rfl
    have O : VG.Proof.Argon2.X86.blk t.mem (VG.Proof.Argon2.X86.op s₀) 0 = xorBlock (VG.Proof.Argon2.X86.working s₄.mem (VG.Proof.Argon2.X86.scr s₀)) (VG.Proof.Argon2.X86.blk s₄.mem (VG.Proof.Argon2.X86.scr s₀) 0) := by
      rw [u.mem, VG.Proof.Argon2.X86.words_zero h₆.out, VG.Proof.Argon2.X86.working_eq,
        VG.Proof.Argon2.X86.blk_of_words (f := fun i => s₄.mem.readW (addr (VG.Proof.Argon2.X86.scr s₀) (1024 + 4 * i)) 32) (fun _ _ => rfl),
        VG.Proof.Argon2.X86.blk_of_words (f := fun i => s₄.mem.readW (addr (VG.Proof.Argon2.X86.scr s₀) (4 * i)) 32)
          (fun i _ => by rw [Nat.zero_add]), VG.Proof.Argon2.X86.xor_words]
      rfl
    show blockAt t.mem ((VG.Proof.Argon2.X86.op s₀).setWidth 64) = _
    rw [VG.Proof.Argon2.X86.blockAt_eq hp.out_fits, O, VG.Proof.Argon2.X86.low_perm fits pf, R₂, st₄.working, st₃.working, W₂, ← X]
    simp only [compress]

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): verified

Constant time, against `compressX86`; then `compressWide`, which lets the
code write its arguments (`Verified.narrowTo`: it only reads them), and the
shared contract `Spec.Argon2.compressContract`, which implies it.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [1024, 4096], argLen := 20,
    argBases := [(12, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Argon2.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.Argon2.X86.τ₀ s := by
  have ho := hp.out_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Argon2.X86.τ₀], by simpa [hp.wr] using hp.out_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_out hp.arg_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Argon2.X86.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : compressX86.pre s₁) (h₂ : compressX86.pre s₂)
    (hpub : compressX86.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Argon2.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.Argon2.X86.pre_of _ h₁; have hp₂ := VG.Proof.Argon2.X86.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Argon2.X86.wf₀ hp₁, VG.Proof.Argon2.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Argon2.X86.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Argon2.X86.outR, VG.Proof.Argon2.X86.scrR, VG.Proof.Argon2.X86.op, VG.Proof.Argon2.X86.scr, ha 2 (by decide), ha 3 (by decide)]
  · simp only [VG.Proof.Argon2.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_fits; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_fits; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem compress_ct : ConstantTime isa compressX86.pre compressX86.pub Impl.Argon2.X86.compress :=
  VG.Taint.constantTime (A := taint) VG.Proof.Argon2.X86.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Argon2.X86.agree₀ h₁ h₂ hpub) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- Memory holding the arguments `0x1000, 0x1400, 0x2000, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x14 else if a = 0x500D then 0x20 else
  if a = 0x5011 then 0x30 else 0

def satState : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Argon2.X86.satMem
  rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩, ⟨0x5004, 16⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩]

theorem sat_pre : compressX86.pre VG.Proof.Argon2.X86.satState := by
  have a0 : arg VG.Proof.Argon2.X86.satState 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Argon2.X86.satState 1 = 0x1400 := by decide
  have a2 : arg VG.Proof.Argon2.X86.satState 2 = 0x2000 := by decide
  have a3 : arg VG.Proof.Argon2.X86.satState 3 = 0x3000 := by decide
  have e : argAddr VG.Proof.Argon2.X86.satState 0 = 0x5004 := by decide
  simp only [VG.Proof.Argon2.X86.compressX86, a0, a1, a2, a3, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem compress_verified : Verified X86.target Impl.Argon2.X86.compress VG.Proof.Argon2.X86.compressX86 :=
  ⟨fun s hs => VG.Proof.Argon2.X86.correct (VG.Proof.Argon2.X86.pre_of s hs), VG.Proof.Argon2.X86.compress_ct, ⟨VG.Proof.Argon2.X86.satState, VG.Proof.Argon2.X86.sat_pre⟩⟩

/-! ## Writable arguments, and the shared contract -/

/-- `compressX86`, with the arguments writable, as `Sig.contract` lays the
regions out. -/
def compressWide : Contract X86.isa :=
  { VG.Proof.Argon2.X86.compressX86 with
    pre := fun s =>
      let x : Region := ⟨(arg s 0).setWidth 64, 1024⟩
      let y : Region := ⟨(arg s 1).setWidth 64, 1024⟩
      let out : Region := ⟨(arg s 2).setWidth 64, 1024⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [x, y] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧
      y.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
      ret.Disjoint scratch ∧
      (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 1024 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 4 + 16 ≤ 2 ^ 32 }

/-- A state satisfying `compressWide.pre`. -/
def satWide : State :=
  { VG.Proof.Argon2.X86.satState with
                  rd := [⟨0x1000, 1024⟩, ⟨0x1400, 1024⟩], wr := [⟨0x2000, 1024⟩, ⟨0x3000, 4096⟩, ⟨0x5004, 16⟩] }

macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [compressX86, compressWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified : Verified X86.target Impl.Argon2.X86.compress VG.Proof.Argon2.X86.compressWide :=
  Verified.narrowTo VG.Proof.Argon2.X86.compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 1024⟩, ⟨(arg s 1).setWidth 64, 1024⟩, ⟨argAddr s 0, 16⟩])
    (fun s => [⟨(arg s 2).setWidth 64, 1024⟩, ⟨(arg s 3).setWidth 64, 4096⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
        by omega⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h)
    ⟨VG.Proof.Argon2.X86.satWide, by
      have a0 : arg VG.Proof.Argon2.X86.satWide 0 = 0x1000 := by decide
      have a1 : arg VG.Proof.Argon2.X86.satWide 1 = 0x1400 := by decide
      have a2 : arg VG.Proof.Argon2.X86.satWide 2 = 0x2000 := by decide
      have a3 : arg VG.Proof.Argon2.X86.satWide 3 = 0x3000 := by decide
      have e : argAddr VG.Proof.Argon2.X86.satWide 0 = 0x5004 := by decide
      simp only [VG.Proof.Argon2.X86.compressWide, a0, a1, a2, a3, e]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
        by decide, by decide⟩ <;>
      exact Region.disjoint_of_sep (by decide)⟩

theorem compress_implies : compressWide.Implies (Spec.Argon2.compressContract X86.abi) := by
  sig_implies [Spec.Argon2.compressContract, Spec.Argon2.compressSig, VG.Proof.Argon2.X86.compressWide, VG.Proof.Argon2.X86.compressX86,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [satWide, satState, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.Argon2.X86.satWide

/-- The emitted function, against the shared contract. -/
theorem compressShared_verified :
    Verified X86.target Impl.Argon2.X86.compress (Spec.Argon2.compressContract X86.abi) :=
  compressWide_verified.of_implies VG.Proof.Argon2.X86.compress_implies

end VG.Proof.Argon2.X86

end
