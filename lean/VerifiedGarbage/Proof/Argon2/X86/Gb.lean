import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Blake2.X86.CompressB.G
import VerifiedGarbage.Proof.Argon2.Spec
import VerifiedGarbage.Impl.Argon2.X86.Compress

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
  gpr : ∀ r, r ∉ temps → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : Keep s s₁) (k₂ : Keep s₁ s₂) : Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr⟩

theorem Keep.of_only {s s' : State} {ds : List Reg} (o : Only ds s s') (h : ∀ r ∈ ds, r ∈ temps) :
    Keep s s' :=
  ⟨fun r hr => o.gpr r fun hd => hr (h r hd), o.rd, o.wr⟩

theorem Keep.of_wrote {s s₁ s₂ : State} {ds : List Reg} {m : Mem} (o : Only ds s s₁)
    (u : Mupd s₁ s₂ m) (h : ∀ r ∈ ds, r ∈ temps) : Keep s s₂ :=
  ⟨fun r hr => by rw [u.gpr]; exact o.gpr r fun hd => hr (h r hd), u.rd.trans o.rd,
    u.wr.trans o.wr⟩

theorem Keep.esi {s s' : State} (k : Keep s s') : s'.gpr .esi = s.gpr .esi := k.gpr _ (by decide)

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
      lo_ofNat]
  · simp only [execMul, RegUpd.gpr_setReg, ite_true, hi_ofNat (mul_lt _ _)]

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
    rw [and_low, and_low, BitVec.ofNat_mul]
  rw [hp, Spec.Argon2.addMul, BitVec.mul_assoc]
  generalize (a &&& 0xffffffff) * (b &&& 0xffffffff) = x
  have two : (2 : BitVec 64) * x = x + x := by bv_omega
  rw [two]
  ac_rfl

section
variable {B : BitVec 32} {N : Nat}

theorem addMul_ok {a b : Nat} (ha : a + 8 ≤ N) (hb : b + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (addMul a b)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B a (Spec.Argon2.addMul (rd64 s.mem B a) (rd64 s.mem B b)) := by
  rw [← List.append_nil (addMul a b)]
  unfold addMul
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem h0 (mem_rd (hA b (by omega)))) fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .esi = B := by rw [u₁.other _ (by decide), h0]
  refine wp_movS (readSrc_mem b₁ (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA a (by omega))))
    fun s₂ u₂ => ?_
  refine wp_mulEdx fun s₃ o₃ p₃ => ?_
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
  rw [← addMul_eq, ← ea, ← ed]
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
    WP isa (.block (xorRot32 d a)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 32) := by
  rw [← List.append_nil (xorRot32 d a)]
  unfold xorRot32
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_st (by rw [o₁.gpr _ (by decide), h0]) (o₁.wr ▸ hA) hd p₁.swap fun s₂ u₂ =>
    WP.block_nil ⟨Keep.of_wrote o₁ u₂ (by decide), by rw [u₂.mem, o₁.mem]⟩

theorem xorRot_ok {d a n : Nat} (hn : 0 < n) (hn' : n < 32) (hd : d + 8 ≤ N) (ha : a + 8 ≤ N)
    {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot d a n)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight n) := by
  rw [← List.append_nil (xorRot d a n)]
  unfold xorRot
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
  refine wp_rot hn hn' (by decide) (by decide) (by decide) p₁ fun s₂ o₂ p₂ => ?_
  have O := o₁.trans o₂
  refine wp_st (by rw [O.gpr _ (by decide), h0]) (O.wr ▸ hA) hd p₂ fun s₃ u₃ =>
    WP.block_nil ⟨Keep.of_wrote O u₃ (by decide), by rw [u₃.mem, O.mem]⟩

theorem xorRot63_ok {d a : Nat} (hd : d + 8 ≤ N) (ha : a + 8 ≤ N) {s : State}
    (h0 : s.gpr .esi = B) (hA : Acc s.wr B N) :
    WP isa (.block (xorRot63 d a)) s fun t => Keep s t ∧
      t.mem = write64 s.mem B d ((rd64 s.mem B d ^^^ rd64 s.mem B a).rotateRight 63) := by
  rw [← List.append_nil (xorRot63 d a)]
  unfold xorRot63
  simp only [List.append_assoc]
  refine xorLd_ok hd ha h0 hA fun s₁ o₁ p₁ => ?_
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
    (working m B)[i] = rd64 m B (wOff i.val) := by
  simp only [working, Fin.getElem_fin, Vector.getElem_ofFn]

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)
include hfit

theorem working_write (m : Mem) (i : Fin 128) (v : Word) :
    working (write64 m B (wOff i.val) v) B = (working m B).set i v := by
  apply Vector.ext
  intro j hj
  simp only [working, Vector.getElem_ofFn, Vector.getElem_set]
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
theorem frame_write (m m' : Mem) (hf : Frame [permR B] m m') (i : Fin 128) (v : Word) :
    Frame [permR B] m (write64 m' B (wOff i.val) v) := by
  have c : ∀ e, e + 4 ≤ 1024 → (permR B).Contains (addr B (1024 + e)) (32 / 8) := fun e he => by
    show (⟨addr B 1024, 1024⟩ : Region).Contains _ _
    rw [addr_off hfit (by omega), addr_off hfit (by omega)]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  have m₁ := List.mem_singleton_self (permR B)
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
  xr b c 63 (am c d (xr d a 16 (am a b (xr b c 24 (am c d (xr d a 32 (am a b v)))))))

set_option linter.unusedSimpArgs false in
theorem gbV_eq {n : Nat} (v : Vector Word n) {a b c d : Fin n} (hab : a.val ≠ b.val)
    (hac : a.val ≠ c.val) (had : a.val ≠ d.val) (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val)
    (hcd : c.val ≠ d.val) : gbV v a b c d = Proof.Argon2.mixWords v a b c d := by
  have nb := Ne.symm hab; have nc := Ne.symm hac; have nd := Ne.symm had
  have nc' := Ne.symm hbc; have nd' := Ne.symm hbd; have nd'' := Ne.symm hcd
  -- The reads at `a`, `b`, `c` and `d` first, then the writes, at any index.
  simp only [gbV, am, xr, Proof.Argon2.mixWords, Proof.Argon2.mix, Fin.getElem_fin,
    Vector.getElem_set_self, Vector.getElem_set_ne _ _ hab, Vector.getElem_set_ne _ _ hac,
    Vector.getElem_set_ne _ _ had, Vector.getElem_set_ne _ _ hbc, Vector.getElem_set_ne _ _ hbd,
    Vector.getElem_set_ne _ _ hcd, Vector.getElem_set_ne _ _ nb, Vector.getElem_set_ne _ _ nc,
    Vector.getElem_set_ne _ _ nd, Vector.getElem_set_ne _ _ nc', Vector.getElem_set_ne _ _ nd',
    Vector.getElem_set_ne _ _ nd'']
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_set]
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
  keep : Keep s t
  working : working t.mem B = v
  frame : Frame [permR B] s.mem t.mem

theorem Step.trans {s t u : State} {v w : Block} (h : Step B s v t) (h' : Step B t w u) :
    Step B s w u := ⟨h.keep.trans h'.keep, h'.working, h.frame.trans h'.frame⟩

include hfit

theorem step_write {s t : State} (k : Keep s t) {i : Fin 128} {x : Word}
    (hm : t.mem = write64 s.mem B (wOff i.val) x) :
    Step B s ((working s.mem B).set i x) t :=
  ⟨k, by rw [hm, working_write hfit], by rw [hm]; exact frame_write hfit _ _ (Frame.refl _ _) i x⟩

theorem Step.am {s t t' : State} {v : Block} (S : Step B s v t) (k : Keep t t') {a b : Fin 128}
    (m : t'.mem = write64 t.mem B (wOff a.val)
      (Spec.Argon2.addMul (rd64 t.mem B (wOff a.val)) (rd64 t.mem B (wOff b.val)))) :
    Step B s (am a b v) t' := by
  have st := step_write hfit k m
  rw [← working_get, ← working_get, S.working] at st
  exact S.trans st

theorem Step.xr {s t t' : State} {v : Block} (S : Step B s v t) (k : Keep t t') {d a : Fin 128} {r : Nat}
    (m : t'.mem = write64 t.mem B (wOff d.val)
      ((rd64 t.mem B (wOff d.val) ^^^ rd64 t.mem B (wOff a.val)).rotateRight r)) :
    Step B s (xr d a r v) t' := by
  have st := step_write hfit k m
  rw [← working_get, ← working_get, S.working] at st
  exact S.trans st

theorem gbAt_ok {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B 4096) (a b c d : Fin 128) :
    WP isa (gbAt a.val b.val c.val d.val) s (Step B s (gbV (working s.mem B) a b c d)) := by
  have o : ∀ i : Fin 128, wOff i.val + 8 ≤ 4096 := fun i => by
    have := i.isLt; simp only [wOff]; omega
  have S₀ : Step B s (working s.mem B) s := ⟨.refl s, rfl, Frame.refl _ _⟩
  have e : ∀ {t : State} {v : Block}, Step B s v t → t.gpr .esi = B := fun S => S.keep.esi.trans h0
  have A : ∀ {t : State} {v : Block}, Step B s v t → Acc t.wr B 4096 := fun S => S.keep.wr ▸ hA
  unfold gbAt gb
  refine WP.block_append ((addMul_ok (o a) (o b) (e S₀) (A S₀)).mono fun s₁ ⟨k₁, m₁⟩ => ?_)
  have S₁ := S₀.am hfit k₁ m₁
  refine WP.block_append ((xorRot32_ok (o d) (o a) (e S₁) (A S₁)).mono fun s₂ ⟨k₂, m₂⟩ => ?_)
  have S₂ := S₁.xr hfit k₂ m₂
  refine WP.block_append ((addMul_ok (o c) (o d) (e S₂) (A S₂)).mono fun s₃ ⟨k₃, m₃⟩ => ?_)
  have S₃ := S₂.am hfit k₃ m₃
  refine WP.block_append ((xorRot_ok (by decide) (by decide) (o b) (o c) (e S₃) (A S₃)).mono
    fun s₄ ⟨k₄, m₄⟩ => ?_)
  have S₄ := S₃.xr hfit k₄ m₄
  refine WP.block_append ((addMul_ok (o a) (o b) (e S₄) (A S₄)).mono fun s₅ ⟨k₅, m₅⟩ => ?_)
  have S₅ := S₄.am hfit k₅ m₅
  refine WP.block_append ((xorRot_ok (by decide) (by decide) (o d) (o a) (e S₅) (A S₅)).mono
    fun s₆ ⟨k₆, m₆⟩ => ?_)
  have S₆ := S₅.xr hfit k₆ m₆
  refine WP.block_append ((addMul_ok (o c) (o d) (e S₆) (A S₆)).mono fun s₇ ⟨k₇, m₇⟩ => ?_)
  have S₇ := S₆.am hfit k₇ m₇
  exact (xorRot63_ok (o b) (o c) (e S₇) (A S₇)).mono fun s₈ ⟨k₈, m₈⟩ => S₇.xr hfit k₈ m₈

end

end VG.Proof.Argon2.X86
