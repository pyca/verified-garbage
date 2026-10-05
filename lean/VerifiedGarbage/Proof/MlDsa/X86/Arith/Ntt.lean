import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.Bfly`. -/
section

/-!
# ML-DSA on x86 (32-bit): the butterflies

With `esi` at coefficient `j` and `edi` at coefficient `j + len` of a
polynomial `G` stored at `p` and `ebp` at the zeta `z` in Montgomery form (`z
· 2³² mod q`, `BIn`), `bflyBody` leaves `bfly G j len z` there and `ibflyBody`
leaves `bflyInv G j len z` (`BOut`), both advancing `esi` and `edi` by 4 and
counting `ecx` down.
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n Poly Zq PolyIs coeffAt)
open VG.Proof.MlKem.X86 (Only wp_cons wp_movm wp_movr wp_mul toNat_ofNat32 eq_ofNat_of_toNat execMul_other)

/-- A butterfly's inputs. -/
structure BIn (s : State) (p : Addr) (G : Poly) (j len : Nat) (zA : Addr) (z : Zq) : Prop where
  ea_i : (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p j
  ea_d : (s.gpr .edi + BitVec.ofNat 32 0).setWidth 64 = coeffAddr p (j + len)
  ea_z : (s.gpr .ebp + BitVec.ofNat 32 0).setWidth 64 = zA
  in_i : InRegions s.wr (coeffAddr p j) 4
  in_d : InRegions s.wr (coeffAddr p (j + len)) 4
  in_z : InRegions (s.rd ++ s.wr) zA 4
  z_v : s.mem.readW zA 32 = BitVec.ofNat 32 (z.val * 2 ^ 32 % q)
  z_sep : Mem.Sep zA 4 (coeffAddr p j) 4
  poly : PolyIs s.mem p G
  hj : j + len < 256
  hl : 0 < len

/-- What a butterfly leaves. -/
structure BOut (s : State) (p : Addr) (G' : Poly) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → r ≠ .esi → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r
  esi : s'.gpr .esi = s.gpr .esi + 4
  edi : s'.gpr .edi = s.gpr .edi + 4
  ecx : s'.gpr .ecx = s.gpr .ecx - 1
  ne : eval .ne s' = some (!(s.gpr .ecx - 1 == 0))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [polyRegion p] s.mem s'.mem
  poly : PolyIs s'.mem p G'

theorem inRd {s : State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- The polynomial `G'` is stored after two coefficients of `G` are written,
if `G'` differs from `G` only there. -/
theorem polyIs_two {m : Mem} {p : Addr} {G G' : Poly} (h : PolyIs m p G) {i₁ i₂ : Nat} (h₁ : i₁ < n)
    (h₂ : i₂ < n) {v₁ v₂ : BitVec 32} (hv₁ : v₁.toNat = (G'[i₁]!).val)
    (hv₂ : v₂.toNat = (G'[i₂]!).val) (hr : ∀ i < n, i ≠ i₁ → i ≠ i₂ → G'[i]! = G[i]!) :
    PolyIs ((m.writeW (coeffAddr p i₁) v₁).writeW (coeffAddr p i₂) v₂) p G' := by
  refine polyIs_of_toNat fun i hi => ?_
  rw [coeffAt_writeW _ _ hi h₂, coeffAt_writeW _ _ hi h₁]
  by_cases e₂ : i₂ = i
  · subst e₂; rw [ite_eq_left rfl, hv₂]
  rw [ite_eq_right e₂]
  by_cases e₁ : i₁ = i
  · subst e₁; rw [ite_eq_left rfl, hv₁]
  rw [ite_eq_right e₁, polyIs_toNat h hi, hr i hi (Ne.symm e₁) (Ne.symm e₂)]

/-- The coefficient stored for `G[i]`. -/
theorem polyIs_coeffAt {m : Mem} {p : Addr} {G : Poly} (h : PolyIs m p G) {i : Nat} (hi : i < n) :
    coeffAt m p i = BitVec.ofNat 32 (G[i]!).val := by
  apply BitVec.eq_of_toNat_eq
  rw [polyIs_toNat h hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt G[i]!; omega)]

theorem bflyBody_eq : bflyBody =
    .mov .eax (.mem (at_ .edi 0)) :: .mov .edx (.mem (at_ .ebp 0)) :: .mul .edx :: (mred .ebx ++
      (([.mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.imm qImm), .alu .sub .eax (.reg .ebx)] : List Instr) ++
        csubQ .eax .edx ++
        ([.store (at_ .edi 0) .eax, .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.reg .ebx)] : List Instr) ++
        csubQ .eax .edx ++
        ([.store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
          .alu .sub .ecx (.imm 1)] : List Instr))) := by
  simp only [bflyBody, List.cons_append, List.nil_append, List.append_assoc]

theorem bfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Zq}
    (h : VG.Proof.MlDsa.X86.Arith.BIn s p G j len zA z) : WP isa (.block bflyBody) s (VG.Proof.MlDsa.X86.Arith.BOut s p (VG.Proof.MlDsa.Arith.bfly G j len z)) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := VG.Proof.MlDsa.X86.Arith.polyIs_coeffAt h.poly hj
  have hb := VG.Proof.MlDsa.X86.Arith.polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := val_lt z
  rw [coeffAt_eq] at ha hb
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  have hzv := h.z_v
  generalize ez : z.val = zv at lz hzv
  have hzm : zv * 2 ^ 32 % q < q := Nat.mod_lt _ (by decide)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 (zv * 2 ^ 32 % q)).toNat = zv * 2 ^ 32 % q := toNat_ofNat32 (mod_q_lt32 _)
  have hbz : b * (zv * 2 ^ 32 % q) < q * 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt lb hzm
    rw [q_eq] at this ⊢; omega
  rw [VG.Proof.MlDsa.X86.Arith.bflyBody_eq]
  refine wp_movm ?_ (wp_movm ?_ (wp_mul (mred_spec (r := .ebx) (by decide) (by decide) _ _ _
    (x := b * (zv * 2 ^ 32 % q)) ?_ hbz fun s₂ o₂ v₂ => ?_)))
  · rw [State.ea, at_]; exact h.ea_d ▸ VG.Proof.MlDsa.X86.Arith.inRd h.in_d
  · simp only [State.ea, at_, State.setReg, show Reg.ebp ≠ Reg.eax by decide, ite_false, h.ea_z]
    exact h.in_z
  · rw [execMul_pair]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, State.setReg, State.ea, at_, h.ea_d, h.ea_z,
      hb, hzv]
    rw [hb', hz']
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [State.setReg, h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [o₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr]; rfl
  have ht : mont (b * (zv * 2 ^ 32 % q)) % q = b * zv % q := mont_mulR b zv
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 (b * zv % q) := eq_ofNat_of_toNat (v₂.trans ht)
  have hrw : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p (j + len)) V).readW (coeffAddr p j) 32 =
      s.mem.readW (coeffAddr p j) 32 := fun V => coeffAt_writeW_ne _ _ hj hjl (by omega) V
  have inI := h.in_i
  have inD := h.in_d
  have inI' := VG.Proof.MlDsa.X86.Arith.inRd h.in_i
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, csubQ, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32, State.store32,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, esi₂, edi₂, ecx₂, m₂,
    rd₂, wr₂, bx₂, ea_i, ea_d, inI, inD, inI', hrw, ha, Option.some.injEq,
    exists_eq_left']
  have lt := Nat.mod_lt (b * zv) (show q > 0 by decide)
  rw [q_eq] at lt
  have e1 : (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 (b * zv % q)).toNat = a + q - b * zv % q := by
    have hQ : (BitVec.ofNat 32 a + qImm).toNat = a + 8380417 := by
      rw [BitVec.toNat_add, toNat_ofNat32 (by omega), qImm_toNat, q_eq, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, toNat_ofNat32 (by rw [q_eq]; omega)]; rw [q_eq]; omega),
      hQ, toNat_ofNat32 (by rw [q_eq]; omega), q_eq]
  have e2 : (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * zv % q)).toNat = a + b * zv % q := by
    rw [BitVec.toNat_add, toNat_ofNat32 (by omega), toNat_ofNat32 (by rw [q_eq]; omega),
      Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
  rw [csubQ_eq (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 (b * zv % q)) _ (by rw [e1, q_eq]; omega),
    csubQ_eq (BitVec.ofNat 32 a + BitVec.ofNat 32 (b * zv % q)) _ (by rw [e2, q_eq]; omega), e1, e2]
  have ht' : (z * G[j + len]!).val = b * zv % q := by
    rw [val_mul, ez, eb, Nat.mul_comm]
  have hv1 : BitVec.ofNat 32 ((a + q - b * zv % q) % q) = BitVec.ofNat 32 ((G[j]! - z * G[j + len]!).val) := by
    rw [sub_val, ht', ea]
  have hv2 : BitVec.ofNat 32 ((a + b * zv % q) % q) = BitVec.ofNat 32 ((G[j]! + z * G[j + len]!).val) := by
    rw [val_add', ht', ea]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h1, h2, h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjl) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)
  · rw [hv1, hv2]
    refine VG.Proof.MlDsa.X86.Arith.polyIs_two h.poly hjl hj ?_ ?_ fun i hi h1 h2 => ?_
    · rw [VG.Proof.MlDsa.Arith.bfly_get _ hl hjl _ hjl, ite_eq_right (by omega), ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! - z * G[j + len]!); omega)
    · rw [VG.Proof.MlDsa.Arith.bfly_get _ hl hjl _ hj, ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! + z * G[j + len]!); omega)
    · rw [VG.Proof.MlDsa.Arith.bfly_get _ hl hjl _ hi, ite_eq_right h2, ite_eq_right h1]

theorem ibflyBody_eq : ibflyBody =
    (([.mov .ebx (.mem (at_ .esi 0)), .alu .add .ebx (.imm qImm), .alu .sub .ebx (.mem (at_ .edi 0)),
      .mov .eax (.mem (at_ .esi 0)), .alu .add .eax (.mem (at_ .edi 0))] : List Instr) ++ csubQ .eax .edx ++
      ([.store (at_ .esi 0) .eax, .mov .eax (.reg .ebx), .mov .edx (.mem (at_ .ebp 0)), .mul .edx] : List Instr)) ++
    (mred .ebx ++ ([.store (at_ .edi 0) .ebx, .alu .add .esi (.imm 4), .alu .add .edi (.imm 4),
      .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [ibflyBody, List.append_assoc]

theorem ibfly_spec {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Zq}
    (h : VG.Proof.MlDsa.X86.Arith.BIn s p G j len zA z) : WP isa (.block ibflyBody) s (VG.Proof.MlDsa.X86.Arith.BOut s p (VG.Proof.MlDsa.Arith.bflyInv G j len z)) := by
  have hj : j < n := by have := h.hj; rw [n_eq]; omega
  have hjl : j + len < n := by have := h.hj; rw [n_eq]; omega
  have hl := h.hl
  have ha := VG.Proof.MlDsa.X86.Arith.polyIs_coeffAt h.poly hj
  have hb := VG.Proof.MlDsa.X86.Arith.polyIs_coeffAt h.poly hjl
  have la := val_lt G[j]!
  have lb := val_lt G[j + len]!
  have lz := val_lt z
  rw [coeffAt_eq] at ha hb
  have hzv := h.z_v
  generalize ea : (G[j]!).val = a at ha la
  generalize eb : (G[j + len]!).val = b at hb lb
  generalize ez : z.val = zv at lz hzv
  have hzm : zv * 2 ^ 32 % q < q := Nat.mod_lt _ (by decide)
  have ha' : (BitVec.ofNat 32 a).toNat = a := toNat_ofNat32 (by omega)
  have hb' : (BitVec.ofNat 32 b).toNat = b := toNat_ofNat32 (by omega)
  have hz' : (BitVec.ofNat 32 (zv * 2 ^ 32 % q)).toNat = zv * 2 ^ 32 % q := toNat_ofNat32 (mod_q_lt32 _)
  have hbz : (a + q - b) * (zv * 2 ^ 32 % q) < q * 2 ^ 32 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a + q - b < 2 * q by rw [q_eq]; omega) hzm
    rw [q_eq] at this ⊢; omega
  have hrz : ∀ V : BitVec 32, (s.mem.writeW (coeffAddr p j) V).readW zA 32 = s.mem.readW zA 32 :=
    fun V => Mem.readW_writeW_sep h.z_sep (by decide)
  have inI := h.in_i
  have inD := h.in_d
  have inI' := VG.Proof.MlDsa.X86.Arith.inRd h.in_i
  have inD' := VG.Proof.MlDsa.X86.Arith.inRd h.in_d
  have inZ := h.in_z
  have ea_i := h.ea_i
  have ea_d := h.ea_d
  have ea_z := h.ea_z
  rw [VG.Proof.MlDsa.X86.Arith.ibflyBody_eq, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, csubQ, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, readSrc, State.ea, at_, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some, ea_i, ea_d,
    ea_z, inI, inI', inD', inZ, ha, hb, hrz, hzv, Option.some.injEq,
    exists_eq_left']
  have hsub : (BitVec.ofNat 32 a + qImm - BitVec.ofNat 32 b).toNat = a + q - b := by
    have hQ : (BitVec.ofNat 32 a + qImm).toNat = a + q := by
      rw [BitVec.toNat_add, ha', qImm_toNat, Nat.mod_eq_of_lt (by rw [q_eq]; omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hQ, hb']; omega), hQ, hb']
  have hsum : (BitVec.ofNat 32 a + BitVec.ofNat 32 b).toNat = a + b := by
    rw [BitVec.toNat_add, ha', hb', Nat.mod_eq_of_lt (by omega)]
  refine mred_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := (a + q - b) * (zv * 2 ^ 32 % q)) ?_ hbz
    fun s₂ o₂ v₂ => ?_
  · rw [execMul_pair]
    simp only [ite_true, ite_false, reduceCtorEq]
    rw [hsub, hz']
  have m₂ := o₂.mem
  simp only [execMul, State.setReg, State.setFlags] at m₂
  rw [csubQ_eq _ _ (by rw [hsum, q_eq]; omega), hsum] at m₂
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [h1, h2, h3, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have edi₂ := g₂ .edi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have rd₂ : s₂.rd = s.rd := by rw [o₂.rd]; rfl
  have wr₂ : s₂.wr = s.wr := by rw [o₂.wr]; rfl
  have ht : mont ((a + q - b) * (zv * 2 ^ 32 % q)) % q = (a + q - b) * zv % q := mont_mulR _ zv
  have bx₂ : s₂.gpr .ebx = BitVec.ofNat 32 ((a + q - b) * zv % q) := eq_ofNat_of_toNat (v₂.trans ht)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    esi₂, edi₂, ecx₂, m₂, rd₂, wr₂, bx₂, ea_d, inD, Option.some.injEq,
    exists_eq_left']
  have hv1 : BitVec.ofNat 32 ((a + b) % q) = BitVec.ofNat 32 ((G[j]! + G[j + len]!).val) := by
    rw [val_add', ea, eb]
  have hv2 : BitVec.ofNat 32 ((a + q - b) * zv % q) =
      BitVec.ofNat 32 ((z * (G[j]! - G[j + len]!)).val) := by
    rw [val_mul, sub_val, ez, ea, eb, Nat.mul_comm zv, Nat.mod_mul_mod]
  refine ⟨fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
  · simp only [h4, h5, h6, ite_false]; exact g₂ r h1 h2 h3
  · simp
  · simp
  · simp
  · simp only [eval, Option.map_some]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj) |>.writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)
  · rw [hv1, hv2]
    refine VG.Proof.MlDsa.X86.Arith.polyIs_two h.poly hj hjl ?_ ?_ fun i hi h1 h2 => ?_
    · rw [VG.Proof.MlDsa.Arith.bflyInv_get _ hl hjl _ hj, ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (G[j]! + G[j + len]!); omega)
    · rw [VG.Proof.MlDsa.Arith.bflyInv_get _ hl hjl _ hjl, ite_eq_right (by omega), ite_eq_left rfl]
      exact toNat_ofNat32 (by have := val_lt (z * (G[j]! - G[j + len]!)); omega)
    · rw [VG.Proof.MlDsa.Arith.bflyInv_get _ hl hjl _ hi, ite_eq_right h1, ite_eq_right h2]

end VG.Proof.MlDsa.X86.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.Table`. -/
section

/-!
# ML-DSA on x86 (32-bit): writing a table of constants

`table t` stores the 256 entries of `t` as words at `[eax]`, through `edx`
(`table_spec`), one entry at a time (`tableN`), so that each step is a short
symbolic execution. The table is read like a polynomial (`coeffAt`).
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n coeffAt)
open VG.Proof.MlKem.X86 (wp_cons wp_store)

/-- `s'` is `s` but for the registers `ds`, the flags and memory. -/
structure Regs (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- Entry `k` of the table. -/
def entry (T : List Nat) (k : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ .eax (4 * k)) .edx]

/-- The first `n` entries. -/
def tableN (T : List Nat) (n : Nat) : List Instr := (List.range n).flatMap (VG.Proof.MlDsa.X86.Arith.entry T)

theorem table_eq (T : List Nat) : table T = VG.Proof.MlDsa.X86.Arith.tableN T 256 := rfl

theorem tableN_succ (t : List Nat) (n : Nat) : VG.Proof.MlDsa.X86.Arith.tableN t (n + 1) = VG.Proof.MlDsa.X86.Arith.tableN t n ++ VG.Proof.MlDsa.X86.Arith.entry t n := by
  simp only [VG.Proof.MlDsa.X86.Arith.tableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` entries of `t` at `p`, from `eax` at `p`: only `edx`, the
flags and the words at `p` change. -/
theorem tableN_spec (t : List Nat) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 256 →
      (∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k) → (∀ k < 256, InRegions s.wr (coeffAddr p k) 4) →
      (∀ s', VG.Proof.MlDsa.X86.Arith.Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) →
      WP isa (.block (VG.Proof.MlDsa.X86.Arith.tableN t n ++ is)) s P
  | 0, is, s, P, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega))
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [VG.Proof.MlDsa.X86.Arith.tableN_succ, List.append_assoc]
    refine VG.Proof.MlDsa.X86.Arith.tableN_spec t n _ s P (by omega) hea hin fun s₁ o₁ f₁ c₁ => ?_
    have ea₁ : s₁.ea (at_ .eax (4 * n)) = coeffAddr p n := by
      rw [← hea n (by omega)]; simp only [State.ea, at_, o₁.gpr .eax (by decide)]
    have hn' : n < Spec.MlDsa.n := by rw [n_eq]; omega
    refine wp_cons (s' := s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0)))
      (by simp only [exec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).wr
        ((s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).ea (at_ .eax (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁, o₁.wr]
      exact hin n (by omega)
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr⟩ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn')
    · intro j hj
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false, ite_true]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlDsa.n by rw [n_eq]; omega) hn']
      by_cases e : n = j
      · rw [ite_eq_left e, e]
      · rw [ite_eq_right e]; exact c₁ j (by omega)

theorem table_spec (t : List Nat) {p : Addr} (is : List Instr) (s : State) (P : State → Prop)
    (hea : ∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k)
    (hin : ∀ k < 256, InRegions s.wr (coeffAddr p k) 4)
    (k : ∀ s', VG.Proof.MlDsa.X86.Arith.Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
      (∀ k < 256, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) :
    WP isa (.block (table t ++ is)) s P := by
  rw [VG.Proof.MlDsa.X86.Arith.table_eq]
  exact VG.Proof.MlDsa.X86.Arith.tableN_spec t 256 is s P (Nat.le_refl _) hea hin k

theorem montZeta_eq {k : Nat} (hk : k < 256) :
    montZetaTable.getD k 0 = (Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← zetaNat_eq]
  exact (by decide +kernel : ∀ k < 256, montZetaTable.getD k 0 = zetaNat k * 2 ^ 32 % 8380417) k hk

theorem montNegZeta_eq {k : Nat} (hk : k < 256) :
    montNegZetaTable.getD k 0 = (-Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← negZetaNat_eq]
  exact (by decide +kernel : ∀ k < 256, montNegZetaTable.getD k 0 = negZetaNat k * 2 ^ 32 % 8380417) k hk

end VG.Proof.MlDsa.X86.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.NttLoop`. -/
section

/-!
# ML-DSA on x86 (32-bit): the layers of the NTT and its inverse

A layer (`Impl.MlKem.X86.layerCode body dz len`) is a loop over its blocks,
each a loop of butterflies `body`; this file proves it once for any butterfly
that computes a function `op` of the polynomial (`Bfly`), with `ebp` moving up
(`dz = zUp`) or down (`zDown`) the table `T` of zetas `zv k` in Montgomery
form, from its entry state `s₀` (`vg_mldsa_ntt(f, scratch)` or
`vg_mldsa_inv_ntt(f, scratch)`, after the setup that stores the table in
`scratch` and `f + 1024` in the argument slot of `scratch`), as for ML-KEM on
x86. The butterflies of a block and the blocks of a layer are the loops
`blockN` and `layerN` of `Proof/MlDsa/Arith/Ntt.lean`.

`MemOK s₀ T G m`: memory holds `G` at `f`, the table, `f` and `f + 1024` in
the argument slots, and differs from the entry only in `f`, `scratch` and
the arguments.
-/

namespace VG.Proof.MlDsa.X86.Arith.NttLoop

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ layerCode blockInit blockEnd zUp zDown)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Spec.MlDsa (q n Poly Zq PolyIs Reduced coeffAt polyAt)
open VG.Proof.MlKem.X86 (E0 P0 P0_esp P0_wr P0_argAddr frameR retR Piece ea_add add_ofNat_add cnt_next cnt_ne
  sub_beq_zero toNat_ofNat32)

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev sP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀), polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀), VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀]
  f_s : (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀))
  f_a : (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)).Disjoint (VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀)
  s_a : (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀)).Disjoint (VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀)
  stk_f : (VG.Proof.MlDsa.X86.Arith.NttLoop.stkR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀))
  stk_s : (VG.Proof.MlDsa.X86.Arith.NttLoop.stkR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀))
  stk_a : (VG.Proof.MlDsa.X86.Arith.NttLoop.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀)
  f_fit : (VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

theorem pub_esp {s₀ s₀' : State} (hq : VG.Proof.MlDsa.X86.Arith.NttLoop.Pub s₀ s₀') : (P0 s₀).gpr .esp = (P0 s₀').gpr .esp := by
  rw [P0_esp, P0_esp, hq.1]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀)
include hp

theorem stk_eq' : VG.Proof.MlDsa.X86.Arith.NttLoop.stkR s₀ = frameR s₀ := VG.Proof.MlDsa.X86.Arith.stk_eq hp.sp

theorem arg_in {i : Nat} (hi : i < 2) : (VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀) k) 4 :=
  ⟨polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_s {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀) k) 4 :=
  ⟨polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀), by rw [hw, P0_wr, hp.wr]; simp, coeff_contains _ (by rw [n_eq]; exact hk)⟩

theorem in_a {s : State} (hw : s.wr = (P0 s₀).wr) {i : Nat} (hi : i < 2) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀, List.mem_append_right _ (by rw [hw, P0_wr, hp.wr]; simp), hp.arg_in hi⟩

end Pre

/-! ## Memory -/

/-- Memory during the layers, holding `G` at `f` and the table `T` at `scratch`. -/
structure MemOK (s₀ : State) (T : List Nat) (G : Poly) (m : Mem) : Prop where
  frame : Frame [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀), polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀), VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀] (P0 s₀).mem m
  tbl : ∀ k < 256, coeffAt m (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀) k = BitVec.ofNat 32 (T.getD k 0)
  arg0 : m.readW (argAddr s₀ 0) 32 = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀
  slot : m.readW (argAddr s₀ 1) 32 = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ + 1024
  poly : PolyIs m (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀) G

/-- Writes to `f` keep the rest. -/
theorem MemOK.step {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀) {T : List Nat} {G G' : Poly} {m m' : Mem} (h : VG.Proof.MlDsa.X86.Arith.NttLoop.MemOK s₀ T G m)
    (hf : Frame [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)] m m') (hG : PolyIs m' (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀) G') : VG.Proof.MlDsa.X86.Arith.NttLoop.MemOK s₀ T G' m' where
  frame := h.frame.trans (hf.mono fun r hr => by simp at hr ⊢; exact .inl hr)
  tbl k hk := by
    rw [coeffAt_congr (m := m) (fun j hj => hf.bytes (R := polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀))
      (by simpa using hp.f_s.symm) (polyLen _) hj) (by rw [n_eq]; omega)]
    exact h.tbl k hk
  arg0 := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.arg0
  slot := by rw [hf.readW (hp.arg_in (by decide)) (by simpa using hp.f_a.symm) (by decide)]; exact h.slot
  poly := hG

/-! ## The butterflies of a block -/

/-- A butterfly code and the function of the polynomial it computes. -/
structure Bfly where
  body : List Instr
  op : Poly → Nat → Nat → Zq → Poly
  spec : ∀ {s : State} {p : Addr} {G : Poly} {j len : Nat} {zA : Addr} {z : Zq},
    VG.Proof.MlDsa.X86.Arith.BIn s p G j len zA z → WP isa (.block body) s (VG.Proof.MlDsa.X86.Arith.BOut s p (op G j len z))

/-- The table `T` holds the zetas `zv` in Montgomery form. -/
def TabOK (T : List Nat) (zv : Nat → Zq) : Prop := ∀ k < 256, T.getD k 0 = (zv k).val * 2 ^ 32 % q

/-- In a block: `t` butterflies done. -/
structure BL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (T : List Nat) (zv : Nat → Zq) (H : Poly)
    (len k start t : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (start + t))
  edi : s.gpr .edi = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (start + len + t))
  ebp : s.gpr .ebp = VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (len - t)
  mem : VG.Proof.MlDsa.X86.Arith.NttLoop.MemOK s₀ T (VG.Proof.MlDsa.Arith.blockN op H len (zv k) start t) s.mem

theorem bfly_step {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀) (b : VG.Proof.MlDsa.X86.Arith.NttLoop.Bfly) {T : List Nat} {zv : Nat → Zq} (hT : VG.Proof.MlDsa.X86.Arith.NttLoop.TabOK T zv)
    {H : Poly} {len k start t : Nat} (hl : 0 < len) (hs : start + 2 * len ≤ 256) (hk : k < 256) (ht : t < len)
    {s : State} (h : VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv H len k start t s) :
    WP isa (.block b.body) s fun s' => VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv H len k start (t + 1) s' ∧
      eval .ne s' = some (decide (t + 1 < len)) := by
  have ff := hp.f_fit
  have fs := hp.s_fit
  have bin : VG.Proof.MlDsa.X86.Arith.BIn s (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀) (VG.Proof.MlDsa.Arith.blockN b.op H len (zv k) start t) (start + t) len (coeffAddr (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀) k) (zv k) := {
    ea_i := by rw [h.esi, ea_add (by omega), Nat.add_zero]
    ea_d := by rw [h.edi, ea_add (by omega), Nat.add_zero]; congr 2; omega
    ea_z := by rw [h.ebp, ea_add (by omega), Nat.add_zero]
    in_i := hp.in_f h.wr (by omega)
    in_d := hp.in_f h.wr (by omega)
    in_z := VG.Proof.MlDsa.X86.Arith.inRd (hp.in_s h.wr (by omega))
    z_v := by rw [← coeffAt_eq, h.mem.tbl k hk, hT k hk]
    z_sep := hp.f_s.symm.sep (coeff_contains _ (by rw [n_eq]; omega)) (coeff_contains _ (by rw [n_eq]; omega))
    poly := h.mem.poly
    hj := by omega
    hl := hl }
  refine (b.spec bin).mono fun s' o => ⟨⟨?_, o.rd.trans h.rd, o.wr.trans h.wr, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [o.esi, h.esi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.edi, h.edi, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · rw [o.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.ebp]
  · rw [o.ecx, h.ecx]; exact cnt_next ht
  · rw [VG.Proof.MlDsa.Arith.blockN_succ]
    exact h.mem.step hp o.frame o.poly
  · rw [o.ne, h.ecx]
    exact (Option.map_some (f := (!·)) _).symm.trans (cnt_ne ht (by omega))

/-! ## The blocks of a layer -/

/-- The zeta of block `c` of the layer with `len`. -/
abbrev zf (zv : Nat → Zq) (kf : Nat → Nat → Nat) (len : Nat) (c : Nat) : Zq := zv (kf len c)

/-- In a layer: `c` blocks done. -/
structure KL (s₀ : State) (op : Poly → Nat → Nat → Zq → Poly) (T : List Nat) (zv : Nat → Zq)
    (kf : Nat → Nat → Nat) (P : Poly) (len c : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ + BitVec.ofNat 32 (4 * (2 * len * c))
  ebp : s.gpr .ebp = VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * kf len c)
  mem : VG.Proof.MlDsa.X86.Arith.NttLoop.MemOK s₀ T (VG.Proof.MlDsa.Arith.layerN op P len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) s.mem

/-- Between layers. -/
structure LB (s₀ : State) (T : List Nat) (G : Poly) (z : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebp : s.gpr .ebp = VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀ + BitVec.ofNat 32 (4 * z)
  mem : VG.Proof.MlDsa.X86.Arith.NttLoop.MemOK s₀ T G s.mem

variable (b : VG.Proof.MlDsa.X86.Arith.NttLoop.Bfly) (T : List Nat) (zv : Nat → Zq) (kf : Nat → Nat → Nat) (P : State → Poly)

theorem blockInit_piece (len c : Nat) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr []) (.block (blockInit len)) hc).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.KL s₀ b.op T zv kf (P s₀) len c s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) len (kf len c) (2 * len * c) 0 s)
      (.block (blockInit len)) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) ht
  apply WP.of_runBlock
  simp only [blockInit, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.map_some,
    Option.bind_some, State.setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨by simp [h.esp], h.rd, h.wr, by simp [h.esi], ?_, by simp [h.ebp], by simp, ?_⟩
  · simp only [show Reg.edi ≠ Reg.ecx by decide, ite_false, ite_true, h.esi]
    rw [add_ofNat_add]; congr 2; omega
  · rw [blockN_zero]; exact h.mem

theorem bflyLoop_piece (hT : VG.Proof.MlDsa.X86.Arith.NttLoop.TabOK T zv) (len c : Nat) (hl : 0 < len) (hs : 2 * len * c + 2 * len ≤ 256)
    (hk : kf len c < 256) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) hc).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) len (kf len c) (2 * len * c) 0 s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) len (kf len c) (2 * len * c) len s)
      (.loop (.block b.body) .ne) :=
  Piece.countLoop hl (fun t s₀ s =>
      VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) len (kf len c) (2 * len * c) t s)
    [.esp, .esi, .edi, .ebp, .ecx]
    (fun t ht s₀ s hp h => VG.Proof.MlDsa.X86.Arith.NttLoop.bfly_step hp b hT hl hs hk ht h)
    (fun t _ s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.esp, h'.esp, VG.Proof.MlDsa.X86.Arith.NttLoop.pub_esp hq]
      · rw [h.esi, h'.esi, VG.Proof.MlDsa.X86.Arith.NttLoop.fP, VG.Proof.MlDsa.X86.Arith.NttLoop.fP, hq.2.1]
      · rw [h.edi, h'.edi, VG.Proof.MlDsa.X86.Arith.NttLoop.fP, VG.Proof.MlDsa.X86.Arith.NttLoop.fP, hq.2.1]
      · rw [h.ebp, h'.ebp, VG.Proof.MlDsa.X86.Arith.NttLoop.sP, VG.Proof.MlDsa.X86.Arith.NttLoop.sP, hq.2.2]
      · rw [h.ecx, h'.ecx]) ht

/-- `ebp` moves up (`zUp`) or down (`zDown`) to the next zeta. -/
def dzOf (up : Bool) : Instr := if up then zUp else zDown

theorem ptr_prev (x : BitVec 32) {a b : Nat} (h : b ≤ a) :
    x + BitVec.ofNat 32 a - BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a - b) := by
  rw [show x + BitVec.ofNat 32 a = x + BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [add_ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

/-- The loop over blocks goes on while blocks are left. -/
theorem blk_cond {len B c : Nat} (hB : len * B = 128) (hc : c < B) :
    (!decide (4 * (2 * len * c + len + len) = 1024)) = decide (c + 1 < B) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  have e : 4 * (2 * len * c + len + len) = 8 * (len * (c + 1)) := by
    rw [Nat.mul_succ, Nat.mul_assoc 2]; omega
  rw [e]
  by_cases h : c + 1 = B
  · rw [h, hB]; simp
  · have hlt : len * (c + 1) < len * B := Nat.mul_lt_mul_of_pos_left (by omega) hl
    rw [hB] at hlt
    simp only [show ¬ 8 * (len * (c + 1)) = 1024 by omega, decide_false, Bool.not_false,
      show c + 1 < B by omega, decide_true]

/-- The pointer compared with the end of `f`. -/
theorem end_cmp (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega)

theorem blockEnd_piece (up : Bool) (len c B : Nat) (hB : len * B = 128) (hc : c < B)
    (hkf : kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : up = false → 1 ≤ kf len c) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (VG.Proof.MlDsa.X86.Arith.NttLoop.dzOf up))) hh).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.BL s₀ b.op T zv (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) c) len (kf len c) (2 * len * c) len s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.KL s₀ b.op T zv kf (P s₀) len (c + 1) s ∧ eval .ne s = some (decide (c + 1 < B)))
      (.block (blockEnd (VG.Proof.MlDsa.X86.Arith.NttLoop.dzOf up))) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have ff := hp.f_fit
    have hsl : (s.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [h.esp]; exact P0_argAddr s₀ 1
    have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 := hp.in_a h.wr (by decide)
    have hlc : 2 * len * c + 2 * len ≤ 256 := by
      have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
      rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega
    apply WP.of_runBlock
    cases up
    all_goals
      simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, blockEnd, VG.Proof.MlDsa.X86.Arith.NttLoop.dzOf, zUp, zDown, runBlock_cons, runStep_some,
        runBlock_nil, exec, execAlu, readSrc, Option.map_some, Option.bind_some, State.setReg, arithFlags,
        State.setFlags, State.ea, at_, State.load32, hsl, ins, h.mem.slot,
        Option.some.injEq, exists_eq_left']
      refine ⟨⟨by simp [h.esp], h.rd, h.wr, ?_, ?_, ?_⟩, ?_⟩
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, Bool.false_eq_true, ite_false]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.MlDsa.X86.Arith.NttLoop.ptr_prev _ (by have := hk rfl; omega)]
      congr 2; have := hk rfl; omega
    · rw [VG.Proof.MlDsa.Arith.layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [VG.Proof.MlDsa.X86.Arith.NttLoop.end_cmp _ (by omega), VG.Proof.MlDsa.X86.Arith.NttLoop.blk_cond hB hc]
    · simp only [show Reg.esi ≠ Reg.ebp by decide, ite_false, ite_true, h.edi]
      congr 2; rw [Nat.mul_succ]; omega
    · simp only [ite_true, h.ebp, hkf, ite_true]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
    · rw [VG.Proof.MlDsa.Arith.layerN_succ]; exact h.mem
    · simp only [eval, Option.map_some, h.edi]
      rw [VG.Proof.MlDsa.X86.Arith.NttLoop.end_cmp _ (by omega), VG.Proof.MlDsa.X86.Arith.NttLoop.blk_cond hB hc]
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, VG.Proof.MlDsa.X86.Arith.NttLoop.pub_esp hq]

theorem layer_piece (hT : VG.Proof.MlDsa.X86.Arith.NttLoop.TabOK T zv) (up : Bool) (len B : Nat) (hB : len * B = 128) (hBp : 0 < B)
    (hkf : ∀ c < B, kf len (c + 1) = if up then kf len c + 1 else kf len c - 1)
    (hk : ∀ c < B, kf len c < 256) (hk1 : up = false → ∀ c < B, 1 ≤ kf len c)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block b.body) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd (VG.Proof.MlDsa.X86.Arith.NttLoop.dzOf up))) h₄).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ T (P s₀) (kf len 0) s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ T (VG.Proof.MlDsa.Arith.layerN b.op (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf zv kf len) B) (kf len B) s)
      (layerCode b.body (VG.Proof.MlDsa.X86.Arith.NttLoop.dzOf up) len) := by
  have hl : 0 < len := by
    rcases Nat.eq_zero_or_pos len with h | h
    · rw [h, Nat.zero_mul] at hB; exact absurd hB (by decide)
    · exact h
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.KL s₀ b.op T zv kf (P s₀) len 0 s) ?_ ((Piece.loop
    (fun c s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.KL s₀ b.op T zv kf (P s₀) len c s) hBp fun c hc =>
      Piece.seq (VG.Proof.MlDsa.X86.Arith.NttLoop.blockInit_piece b T zv kf P len c t₂)
        (Piece.seq (VG.Proof.MlDsa.X86.Arith.NttLoop.bflyLoop_piece b T zv kf P hT len c hl ?_ (hk c hc) t₃)
          (VG.Proof.MlDsa.X86.Arith.NttLoop.blockEnd_piece b T zv kf P up len c B hB hc (hkf c hc) (fun e => hk1 e c hc) t₄))).mono
    (fun _ _ _ h => h) fun _ _ _ h => ⟨h.esp, h.rd, h.wr, h.ebp, h.mem⟩)
  · refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) t₁
    · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
        rw [h.esp]; exact P0_argAddr s₀ 0
      have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
        State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [h.esp], h.rd, h.wr, by simp, by simp [h.ebp], ?_⟩
      rw [layerN_zero]; exact h.mem
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, VG.Proof.MlDsa.X86.Arith.NttLoop.pub_esp hq]
  · have : len * (c + 1) ≤ len * B := Nat.mul_le_mul_left _ hc
    rw [Nat.mul_succ] at this; rw [Nat.mul_assoc]; omega

end VG.Proof.MlDsa.X86.Arith.NttLoop

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.NttSetup`. -/
section

/-!
# ML-DSA on x86 (32-bit): the start of `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

Both load `scratch` into `eax` (`ld_piece`), store a table there, point `ebp`
at entry `z`, and store `f + 1024` in the argument slot of `scratch`
(`setup_piece`), leaving `MemOK` with the input polynomial, as for ML-KEM on
x86.
-/

namespace VG.Proof.MlDsa.X86.Arith.NttLoop

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Spec.MlDsa (q n Poly Zq PolyIs Reduced coeffAt polyAt inPlaceContract inPlaceSig)
open VG.Proof.MlKem.X86 (E0 P0 P0_esp P0_wr P0_argAddr P0_argIn P0_arg frameR retR Piece ea_off)

theorem Pre.of {s₀ : State} {stk : Nat} {t : Poly → Poly}
    (h : (inPlaceContract X86.abi t stk).pre s₀) (hs : stk = 16) : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀ := by
  subst hs
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- After `ldScratch`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀

theorem ld_piece : Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => s = P0 s₀) VG.Proof.MlDsa.X86.Arith.NttLoop.S1 (.block ldScratch) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₁ := P0_argAddr s₀ 1
    have i₁ := P0_argIn (s₀ := s₀) (n := 2) (i := 1) (by omega) fit (by simp [hp.wr])
    have v₁ := P0_arg hp.sp (n := 2) (i := 1) (by omega) fit (by
      simpa [← hp.stk_eq'] using hp.stk_a)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [ldScratch, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₁, i₁, v₁, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', VG.Proof.MlDsa.X86.Arith.NttLoop.pub_esp hq]

theorem arg01_sep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀) : Mem.Sep (argAddr s₀ 0) 4 (argAddr s₀ 1) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  bv_omega

theorem Pre.P0_keep {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := VG.Proof.MlDsa.X86.Arith.P0_mem hp.sp

theorem setup_piece (T : List Nat) (z : Nat) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .eax]) (.block (nttSetup T z)) hh).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub VG.Proof.MlDsa.X86.Arith.NttLoop.S1 (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ T (polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)) z s) (.block (nttSetup T z)) := by
  refine Piece.taint [.esp, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have fs := hp.s_fit
    have fit := hp.sp'
    rw [nttSetup]
    refine VG.Proof.MlDsa.X86.Arith.table_spec T (p := VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀) _ s _
      (fun k hk => by
        show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
        rw [h.eax, ea_off (by omega)])
      (fun k hk => hp.in_s h.wr (by omega)) fun s₁ o₁ f₁ c₁ => ?_
    have esp₁ : s₁.gpr .esp = (P0 s₀).gpr .esp := by rw [o₁.gpr .esp (by decide), h.esp]
    have eax₁ : s₁.gpr .eax = VG.Proof.MlDsa.X86.Arith.NttLoop.sP s₀ := by rw [o₁.gpr .eax (by decide), h.eax]
    have wr₁ : s₁.wr = (P0 s₀).wr := o₁.wr.trans h.wr
    have rd₁ : s₁.rd = (P0 s₀).rd := o₁.rd.trans h.rd
    have a20 : (s₁.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
      rw [esp₁]; exact P0_argAddr s₀ 0
    have a24 : (s₁.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [esp₁]; exact P0_argAddr s₀ 1
    have in0 : InRegions (s₁.rd ++ s₁.wr) (argAddr s₀ 0) 4 := hp.in_a wr₁ (by decide)
    have in1 : InRegions s₁.wr (argAddr s₀ 1) 4 :=
      ⟨VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀, by rw [wr₁, P0_wr, hp.wr]; simp, hp.arg_in (by decide)⟩
    have hsa : ∀ r ∈ [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀)], (⟨argAddr s₀ 0, 4⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton, forall_eq]
      exact (hp.s_a.symm.sub_left fun x hx => by
        have := hp.arg_in (i := 0) (by decide)
        simp only [Region.Contains] at hx this ⊢; omega)
    have v0 : s₁.mem.readW (argAddr s₀ 0) 32 = VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ := by
      rw [f₁.readW (Region.contains_self _ _) hsa (by decide), h.mem]
      exact P0_arg hp.sp (n := 2) (i := 0) (by omega) fit (by simpa [← hp.stk_eq'] using hp.stk_a)
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.ea, at_, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a20, a24, in0, in1, v0, Option.some.injEq,
      exists_eq_left']
    have hs1 : Frame [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀)] (P0 s₀).mem s₁.mem := h.mem ▸ f₁
    refine ⟨by simp [esp₁], rd₁, wr₁, by simp [eax₁], ?_, ?_, ?_, ?_, ?_⟩
    · exact (hs1.mono fun r hr => by simp at hr ⊢; exact .inr (.inl hr)).writeW (by simp) _
        (hp.arg_in (by decide))
    · intro k hk
      rw [coeffAt_eq, Mem.readW_writeW_sep (Region.Disjoint.sep hp.s_a (coeff_contains _ (by rw [n_eq]; omega))
        (hp.arg_in (by decide))) (by decide), ← coeffAt_eq, c₁ k hk]
    · rw [Mem.readW_writeW_sep (VG.Proof.MlDsa.X86.Arith.NttLoop.arg01_sep hp) (by decide), v0]
    · exact Mem.readW_writeW_self32 _ _ _
    · have fr : Frame [frameR s₀, polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀), VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀] s₀.mem
          (s₁.mem.writeW (argAddr s₀ 1) (VG.Proof.MlDsa.X86.Arith.NttLoop.fP s₀ + 1024)) :=
        ((hp.P0_keep.mono (by simp)).trans (hs1.mono (by simp))).writeW (by simp) _ (hp.arg_in (by decide))
      refine polyIs_frame fr (fun r hr => ?_) ⟨hp.f_red, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hp.stk_eq']; exact hp.stk_f.symm
      · exact hp.f_s
      · exact hp.f_a
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, VG.Proof.MlDsa.X86.Arith.NttLoop.pub_esp hq]
    · rw [h.eax, h'.eax, VG.Proof.MlDsa.X86.Arith.NttLoop.sP, VG.Proof.MlDsa.X86.Arith.NttLoop.sP, hq.2.2]

/-- The regions the body writes. -/
abbrev W (s₀ : State) : List Region := [polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀), polyRegion (VG.Proof.MlDsa.X86.Arith.NttLoop.sA s₀), VG.Proof.MlDsa.X86.Arith.NttLoop.aR s₀]

theorem hW {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.NttLoop.Pre s₀) : ∀ r ∈ VG.Proof.MlDsa.X86.Arith.NttLoop.W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨by rw [← hp.stk_eq']; exact hp.stk_f, hp.ret_f⟩
  · exact ⟨by rw [← hp.stk_eq']; exact hp.stk_s, hp.ret_s⟩
  · exact ⟨by rw [← hp.stk_eq']; exact hp.stk_a, hp.ret_a⟩

theorem nil_piece {A : State → State → Prop} : Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub A A (.block []) :=
  Piece.taint [] (fun _ _ _ h => WP.block_nil_iff.mpr h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

end VG.Proof.MlDsa.X86.Arith.NttLoop

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt`

The eight layers of Algorithm 41 (`ntt_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `bflyBody` (`bfly_spec`), with the zetas
from `zetas 1` up.
-/

namespace VG.Proof.MlDsa.X86.Arith.NttFwd

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch layerCode layers blockInit blockEnd zUp)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Proof.MlDsa.X86.Arith.NttLoop
open VG.Spec.MlDsa (q n Poly Zq PolyIs Reduced coeffAt polyAt nttContract inPlaceContract inPlaceSig zetas)
open VG.Proof.MlKem.X86 (E0 P0 frameR retR Piece LeafPost satState)

/-- The butterfly of Algorithm 41. -/
def bf : VG.Proof.MlDsa.X86.Arith.NttLoop.Bfly := ⟨bflyBody, VG.Proof.MlDsa.Arith.bfly, VG.Proof.MlDsa.X86.Arith.bfly_spec⟩

/-- The table entry of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 128 / len + c

theorem tab : VG.Proof.MlDsa.X86.Arith.NttLoop.TabOK montZetaTable VG.Spec.MlDsa.zetas := fun _ hk => VG.Proof.MlDsa.X86.Arith.montZeta_eq hk

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 128 / len + B ≤ 256) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block bflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zUp)) h₄).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (P s₀) (VG.Proof.MlDsa.X86.Arith.NttFwd.kf len 0) s)
      (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (VG.Proof.MlDsa.Arith.layerN VG.Proof.MlDsa.Arith.bfly (P s₀) len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf VG.Spec.MlDsa.zetas VG.Proof.MlDsa.X86.Arith.NttFwd.kf len) B) (VG.Proof.MlDsa.X86.Arith.NttFwd.kf len B) s)
      (layerCode bflyBody zUp len) :=
  VG.Proof.MlDsa.X86.Arith.NttLoop.layer_piece VG.Proof.MlDsa.X86.Arith.NttFwd.bf montZetaTable VG.Spec.MlDsa.zetas VG.Proof.MlDsa.X86.Arith.NttFwd.kf P VG.Proof.MlDsa.X86.Arith.NttFwd.tab true len B hB hBp (fun c _ => by simp [VG.Proof.MlDsa.X86.Arith.NttFwd.kf]; omega)
    (fun c hc => by simp only [VG.Proof.MlDsa.X86.Arith.NttFwd.kf]; omega) (fun h => absurd h (by decide)) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.NttLoop.fA s₀)

theorem nttLayer_eq (f : Poly) (len : Nat) : VG.Proof.MlDsa.Arith.nttLayer f len = VG.Proof.MlDsa.Arith.layerN VG.Proof.MlDsa.Arith.bfly f len (VG.Proof.MlDsa.X86.Arith.NttLoop.zf VG.Spec.MlDsa.zetas VG.Proof.MlDsa.X86.Arith.NttFwd.kf len) (128 / len) :=
  rfl

example : True := by
  have := VG.Proof.MlDsa.X86.Arith.NttFwd.lay 128 1 (by decide) (by decide) (by decide) VG.Proof.MlDsa.X86.Arith.NttFwd.F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)
  trivial

theorem fold_eq (f : Poly) : nttLens.foldl VG.Proof.MlDsa.Arith.nttLayer f =
    VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer f 128) 64) 32) 16) 8) 4) 2) 1 := by
  simp only [VG.Proof.MlDsa.Arith.nttLens, List.foldl_cons, List.foldl_nil]

theorem layers_piece : Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 1 s)
    (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (nttLens.foldl VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀)) 256 s)
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]) := by
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 128 1 (by decide) (by decide) (by decide) VG.Proof.MlDsa.X86.Arith.NttFwd.F (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 64 2 (by decide) (by decide) (by decide) (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 32 4 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 16 8 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64) 32)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 8 16 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64) 32) 16)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 4 32 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64) 32) 16) 8)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 2 64 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64) 32) 16) 8) 4)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (VG.Proof.MlDsa.X86.Arith.NttFwd.lay 1 128 (by decide) (by decide) (by decide)
    (fun s₀ => VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀) 128) 64) 32) 16)
      8) 4) 2)
    (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [VG.Proof.MlDsa.X86.Arith.NttFwd.fold_eq]; exact h

theorem body_piece : Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (nttLens.foldl VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀)) 256 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup montZetaTable 1))
      (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]))) :=
  Piece.seq VG.Proof.MlDsa.X86.Arith.NttLoop.ld_piece (Piece.seq (VG.Proof.MlDsa.X86.Arith.NttLoop.setup_piece montZetaTable 1 (by taint_decide)) VG.Proof.MlDsa.X86.Arith.NttFwd.layers_piece)

theorem piece : Piece VG.Proof.MlDsa.X86.Arith.NttLoop.Pre VG.Proof.MlDsa.X86.Arith.NttLoop.Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => VG.Proof.MlDsa.X86.Arith.NttLoop.LB s₀ montZetaTable (nttLens.foldl VG.Proof.MlDsa.Arith.nttLayer (VG.Proof.MlDsa.X86.Arith.NttFwd.F s₀)) 256 s) s₀ s')
    Impl.MlDsa.X86.Arith.ntt :=
  Piece.leaf VG.Proof.MlDsa.X86.Arith.NttLoop.W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp => VG.Proof.MlDsa.X86.Arith.NttLoop.hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.mem.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlDsa.ntt) h rfl) fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm, VG.Proof.MlDsa.Arith.ntt_eq_layers]
    exact hinv.mem.poly
  · let st := satState VG.Proof.MlDsa.X86.Arith.NttLoop.satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [VG.Proof.MlDsa.X86.Arith.NttLoop.satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)])
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith.NttFwd

end
